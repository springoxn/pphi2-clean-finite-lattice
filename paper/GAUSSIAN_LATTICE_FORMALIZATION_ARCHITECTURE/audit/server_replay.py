#!/usr/bin/env python3
"""Run isolated pinned Lean builds and contracts on the Linux server only."""
from pathlib import Path
import datetime
import hashlib
import json
import platform
import re
import subprocess
import sys

LAKE = '/home/zhengyj/.elan/bin/lake'
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if platform.system() != 'Linux' or not Path(LAKE).is_file():
        raise RuntimeError('This runner must execute on the designated Linux Lean server')
    sources = ROOT / 'sources'
    out = ROOT / 'results'
    out.mkdir(exist_ok=True)
    expected = json.loads((sources / 'expected.json').read_text())
    actual = {name: digest(sources / name) for name in expected}
    assert actual == expected, 'Transferred source bytes changed'
    result = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'server': platform.node(), 'system': platform.platform(),
              'lake': LAKE, 'source_sha256': actual, 'steps': [],
              'scope': 'Pinned local Gaussian endpoints only; no upstream build or interacting-proof certification.'}
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    specs = [
        ('dimensional', 'main', '/home/zhengyj/AImath-lean/AImathPPhi2Clean/.lake/packages',
         ['AImathPPhi2Clean.PeriodicHMinusThreeWeakLimitMarginal',
          'AImathPPhi2Clean.Periodic3DHminusThreeMarginals',
          'AImathPPhi2Clean.Periodic3DGaussianFourierMarginals',
          'AImathPPhi2Clean.PeriodicFS4DProbeMoment'],
         ['audit/architecture_2d_endpoint.lean', 'audit/periodic3d_hminus3_endpoint.lean',
          'audit/fs3_periodic_raw_lift_interface.lean', 'audit/fs4_periodic_raw_lift_interface.lean']),
        ('generic', 'generic', '/home/zhengyj/AImath-lean/ArbitraryDimRawGaussian/.lake/packages',
         ['AImathPPhi2Clean.ActualWeakLimitArbitraryDim'],
         ['SharpContractArbitraryDim.lean', 'EndpointContractArbitraryDim.lean']),
        ('five', 'five', '/home/zhengyj/AImath-lean/Dim122409RawGaussian/.lake/packages',
         ['AImathPPhi2Clean.Periodic5DGaussianMarginals'],
         ['audit/periodic5d_hminus3_endpoint.lean']),
    ]
    failed = False
    for label, folder, deps, targets, contracts in specs:
        project = sources / folder
        lake_dir = project / '.lake'
        lake_dir.mkdir(exist_ok=True)
        packages = lake_dir / 'packages'
        if not packages.exists():
            packages.symlink_to(deps, target_is_directory=True)
        assert (packages / 'mathlib').exists(), deps
        lock_before = digest(project / 'lake-manifest.json')
        steps = [('version', [LAKE, 'env', 'lean', '--version'], False),
                 ('build', [LAKE, 'build', *targets], False)]
        steps += [(Path(contract).stem, [LAKE, 'env', 'lean', contract], True) for contract in contracts]
        for name, command, contract in steps:
            log = out / (label + '-' + name + '.log')
            with log.open('w') as fh:
                fh.write('CWD=' + str(project) + '\nCOMMAND=' + json.dumps(command) + '\n')
                fh.flush()
                proc = subprocess.run(command, cwd=project, stdout=fh, stderr=subprocess.STDOUT)
                fh.write('\nEXIT=' + str(proc.returncode) + '\n')
            text = log.read_text()
            reports = re.findall(r'depends on axioms:\s*\[([^]]*)\]', text, re.S)
            ok = proc.returncode == 0 and 'sorryAx' not in text
            if contract:
                ok = ok and bool(reports) and all(
                    {x.strip() for x in report.split(',') if x.strip()} <= ALLOW for report in reports)
            result['steps'].append({'project': label, 'name': name, 'command': command,
                                    'cwd': str(project), 'exit': proc.returncode, 'pass': ok,
                                    'axiom_reports': len(reports), 'log': log.name,
                                    'sha256': digest(log)})
            print(label, name, 'PASS' if ok else 'FAIL', flush=True)
            (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
            if not ok:
                failed = True
                break
        assert digest(project / 'lake-manifest.json') == lock_before, 'Dependency lock changed'
    assert {name: digest(sources / name) for name in expected} == expected, 'Source changed during replay'
    result['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result['status'] = 'FAIL' if failed else 'PASS'
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
