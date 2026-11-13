#!/usr/bin/env python3
"""Check pinned sources, fresh server replay evidence, authorship and the rendered PDF."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import re
import sys
import zipfile
import fitz

ROOT = Path(__file__).resolve().parents[1]
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def verify_hash(data, expected):
    require(sha(data) == expected, 'hash mismatch')


def axioms(text):
    require('sorryAx' not in text and not re.search(r'^error:', text, re.M), 'failed transcript')
    reports = re.findall(r'depends on axioms:\s*\[([^]]*)\]', text, re.S)
    require(bool(reports), 'missing axiom report')
    for report in reports:
        names = {v.strip() for v in report.split(',') if v.strip()}
        require(names <= ALLOW, 'unexpected axiom')
    return len(reports)


def has_anchor(source, anchor):
    require(anchor in source, 'missing declaration: ' + anchor)


def server_replay():
    folder = ROOT / 'evidence/server_replay'
    result = json.loads((folder / 'result.json').read_text())
    require(result['status'] == 'PASS', 'server replay did not pass')
    require(result['lake'] == '/home/zhengyj/.elan/bin/lake', 'unexpected server Lean executable')
    expected = {
        ('dimensional', 'version'), ('dimensional', 'build'),
        ('dimensional', 'architecture_2d_endpoint'), ('dimensional', 'periodic3d_hminus3_endpoint'),
        ('dimensional', 'fs3_periodic_raw_lift_interface'), ('dimensional', 'fs4_periodic_raw_lift_interface'),
        ('generic', 'version'), ('generic', 'build'), ('generic', 'SharpContractArbitraryDim'),
        ('generic', 'EndpointContractArbitraryDim'), ('five', 'version'), ('five', 'build'),
        ('five', 'periodic5d_hminus3_endpoint'),
    }
    require({(s['project'], s['name']) for s in result['steps']} == expected, 'incomplete server replay scope')
    reports = 0
    for step in result['steps']:
        require(step['pass'] and step['exit'] == 0, 'failed server step')
        data = (folder / step['log']).read_bytes()
        verify_hash(data, step['sha256'])
        text = data.decode('utf-8')
        require('EXIT=0' in text, 'missing server exit marker')
        require(step['command'][0] == result['lake'], 'server command differs')
        if step['name'] not in {'build', 'version'}:
            reports += axioms(text)
        elif step['name'] == 'build':
            require('Build completed successfully' in text, 'missing successful server build')
        else:
            require('4.34.0-rc2' in text, 'unexpected Lean version')
    source_hashes = result['source_sha256']
    release = ROOT / 'evidence/release'
    for p in (release / 'AImathPPhi2Clean').rglob('*.lean'):
        key = 'main/' + p.relative_to(release).as_posix()
        verify_hash(p.read_bytes(), source_hashes[key])
    generic = release / 'projects/ARBITRARY_DIM_RAW_GAUSSIAN'
    for p in generic.rglob('*'):
        if p.is_file() and (p.suffix == '.lean' or p.name in {'lake-manifest.json', 'lean-toolchain'}):
            verify_hash(p.read_bytes(), source_hashes['generic/' + p.relative_to(generic).as_posix()])
    archive = release / 'paper/PERIODIC_GAUSSIAN_5D_HMINUS3/periodic_gaussian_5d_hminus3_endpoint.zip'
    with zipfile.ZipFile(archive) as z:
        for name in z.namelist():
            if name.endswith('.lean') or name in {'lake-manifest.json', 'lean-toolchain'}:
                verify_hash(z.read(name), source_hashes['five/' + name])
    return len(result['steps']), reports


def main():
    entries = json.loads((ROOT / 'audit/source_manifest.json').read_text())
    for name, expected in entries.items():
        verify_hash((ROOT / name).read_bytes(), expected)
    release = ROOT / 'evidence/release'
    generic = release / 'projects/ARBITRARY_DIM_RAW_GAUSSIAN'
    generic_hashes = 0
    for line in (generic / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        verify_hash((generic / name).read_bytes(), digest)
        generic_hashes += 1
    anchors = {
        'PeriodicHMinusThreeWeakLimitMarginal.lean': 'periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders',
        'Periodic3DHminusThreeWeakLimit.lean': 'periodic3DGaussianTargetH3_map_inclusion',
        'PeriodicFS4DProbeMoment.lean': 'fs4PeriodicFixedVolume_weak_tendsto_free',
    }
    for name, anchor in anchors.items():
        has_anchor((release / 'AImathPPhi2Clean' / name).read_text(encoding='utf-8'), anchor)
    has_anchor((generic / 'SharpContractArbitraryDim.lean').read_text(encoding='utf-8'),
               'sharp_actual_raw_gaussian_weak_convergence')
    reports = 0
    for rel in ['sharp-contract.log', 'endpoint-contract.log', 'parent-sharp-contract.log']:
        reports += axioms((generic / rel).read_text(encoding='utf-8'))
    for rel in ['audit/periodic3d_hminus3_endpoint.log', 'audit/periodic5d_hminus3_endpoint.log',
                'paper/PERIODIC_GAUSSIAN_DIMENSION_BRIDGE/audit/bridge_contract.log']:
        reports += axioms((release / rel).read_text(encoding='utf-8'))
    log = (generic / 'build-sharp.log').read_text(encoding='utf-8')
    require('Build completed successfully' in log and 'EXIT=0' in log, 'missing recorded build success')
    archive = release / 'paper/PERIODIC_GAUSSIAN_5D_HMINUS3/periodic_gaussian_5d_hminus3_endpoint.zip'
    verify_hash(archive.read_bytes(), '3424b3573469c4f894efdfc911922a6348fb9e15f3302de0c56a047a460c06b9')
    with zipfile.ZipFile(archive) as z:
        matches = [n for n in z.namelist() if n.endswith('/Periodic5DWeakLimit.lean')]
        require(len(matches) == 1, 'missing 5D weak-limit source')
        has_anchor(z.read(matches[0]).decode('utf-8'), 'periodic5DFixedVolume_weak_limit_existsUnique')
    upstream = ROOT / 'evidence/upstream'
    has_anchor((upstream / 'OSforGFF/OSforGFF/OS/Master.lean').read_text(encoding='utf-8'),
               'gaussianFreeField_satisfies_all_OS_axioms_of_dim')
    has_anchor((upstream / 'bochner/Minlos/Main.lean').read_text(encoding='utf-8'), 'minlos_theorem')
    ci = json.loads((upstream / 'osforgff_ci.json').read_text())
    require(ci['head_sha'] == 'fef84a82937dfd2bb7f672108a72da329d3ef0fd' and ci['conclusion'] == 'success', 'upstream CI pin')
    snapshot = json.loads((ROOT / 'evidence/scope_snapshot.json').read_text())['nodes']
    for key in ['INTERACTING_SCALAR_2D_COMPLETE', 'PPHI2_OS_POSITIVITY', 'RP_COVARIANCE']:
        require(snapshot[key]['status'] == 'PROVED_PAPER', 'scope status differs')
    require(snapshot['OS_RECONSTRUCTION']['status'] == 'LITERATURE', 'reconstruction scope differs')
    for d, s, r in [(2, 3, Fraction(2)), (3, 3, Fraction(9, 4)), (4, 4, Fraction(3)), (5, 3, Fraction(11, 4))]:
        require((Fraction(s) + Fraction(d, 2)) / 2 == r, 'midpoint arithmetic')
        require(Fraction(d, 2) < r < s, 'positive compactness gap')
    for radius in range(1, 100):
        old = Fraction(1, radius ** 6)
        new = Fraction(1, (1 + radius) ** 6)
        require(old / 64 <= new <= old, '2D weight comparison')
    rejected = 0
    for action in [lambda: verify_hash(b'changed', sha(b'original')),
                   lambda: axioms("'t' depends on axioms: [sorryAx]"),
                   lambda: axioms("'t' depends on axioms: [unknownAxiom]"),
                   lambda: has_anchor('wrong source', 'expected_theorem')]:
        try:
            action()
        except AssertionError:
            rejected += 1
    require(rejected == 4, 'negative controls failed')
    tex = (ROOT / 'main.tex').read_text(encoding='utf-8')
    require(r'\author{YJ ZHENG}' in tex, 'required author is YJ ZHENG')
    cites = {v for group in re.findall(r'\\cite\{([^}]+)\}', tex) for v in group.split(',')}
    bib = set(re.findall(r'\\bibitem\{([^}]+)\}', tex))
    require(cites <= bib, 'undefined citation')
    refs = set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex))
    labels = set(re.findall(r'\\label\{([^}]+)\}', tex))
    require(refs <= labels, 'undefined cross reference')
    pdf = ROOT / 'main.pdf'
    doc = fitz.open(pdf)
    text = ' '.join(' '.join(p.get_text().split()) for p in doc)
    require('YJ ZHENG' in doc[0].get_text(), 'author missing from first PDF page')
    require(doc.metadata.get('author') == 'YJ ZHENG', 'PDF author metadata differs')
    for phrase in ['Two through five dimensions', 'Reusable interfaces', 'Relation to Lean probability',
                   'wider research programme', 'Evidence ledger', 'References']:
        require(phrase.lower() in text.lower(), 'missing PDF section: ' + phrase)
    captions = len(re.findall(r'\bTable\s+[123][.:]', text))
    require(captions == 3, 'missing or duplicated table caption')
    require('\ufffd' not in text, 'replacement glyph')
    for page in doc:
        require(bool(page.get_text().strip()), 'blank page')
        for block in page.get_text('dict')['blocks']:
            for line in block.get('lines', []):
                for span in line['spans']:
                    x0, y0, x1, y1 = span['bbox']
                    require(x0 >= -1 and y0 >= -1 and x1 <= page.rect.width + 1 and y1 <= page.rect.height + 1,
                            'text outside page')
    logpath = ROOT / 'build/second/main.log'
    warnings = []
    if logpath.exists():
        log = logpath.read_text(encoding='utf-8')
        warnings = re.findall(r'Overfull \\hbox[^\n]*', log)
        require(not warnings, 'overfull horizontal boxes: ' + repr(warnings))
    server_steps, server_reports = server_replay()
    result = {'status': 'PASS', 'source_manifest_files': len(entries), 'generic_manifest_files': generic_hashes,
              'recorded_axiom_reports': reports, 'server_replay_steps': server_steps,
              'server_replay_axiom_reports': server_reports, 'author': 'YJ ZHENG',
              'negative_controls': rejected, 'pdf_pages': len(doc),
              'pdf_table_captions': captions, 'overfull_hboxes': len(warnings), 'pdf_sha256': sha(pdf.read_bytes()),
              'evidence_boundary': 'Hash/source/transcript/PDF audit, including fresh isolated server builds and local Gaussian endpoint replays. No independent upstream build or interacting-proof certification.'}
    (ROOT / 'audit/result.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except AssertionError as exc:
        print('AUDIT FAIL:', exc, file=sys.stderr)
        sys.exit(1)
    except Exception as exc:
        print('AUDIT ERROR:', exc, file=sys.stderr)
        sys.exit(2)
