#!/usr/bin/env python3
"""Run every clean interface certificate and reject every non-base axiom.
Runs after lake build. Includes parser negative controls for custom axioms,
sorryAx, empty reports, and Lean errors; wrapped axiom lists are supported.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
# The Lean executable is taken from the environment so the gate is portable:
#     LAKE=/path/to/lake python audit/run_interface_gate.py
# with a fallback to the elan-managed toolchain this project pins.
LAKE = (os.environ.get('LAKE')
        or shutil.which('lake')
        or str(Path.home() / '.elan' / 'toolchains'
               / 'leanprover--lean4---v4.34.0-rc2' / 'bin' / 'lake'))
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}

def validate(text, expected):
    if re.search(r'\berror:', text):
        raise ValueError('Lean error')
    records = re.findall(r"^'(.*)' depends on axioms: \[([^\]]*)\]", text, re.M)
    empty = re.findall(r"^'(.*)' does not depend on any axioms", text, re.M)
    if {name for name, _ in records} | set(empty) != set(expected):
        raise ValueError('missing or unexpected declaration records')
    for name, body in records:
        bad = {a.strip() for a in body.split(',') if a.strip()} - ALLOW
        if bad:
            raise ValueError(f'{name}: forbidden axioms {sorted(bad)}')

validate("'good' depends on axioms: [propext,\n Classical.choice, Quot.sound]", ['good'])
for text in ["'bad' depends on axioms: [injectedAxiom]",
             "'bad' depends on axioms: [sorryAx]", '',
             "error: failure\n'bad' depends on axioms: []"]:
    try:
        validate(text, ['bad'])
    except ValueError:
        pass
    else:
        raise SystemExit('FAIL: parser negative control accepted pollution')

queries = [ROOT / 'audit/clean_axioms.lean', *sorted((ROOT / 'audit').glob('*_interface.lean'))]
for query in queries:
    expected = re.findall(r'^#print axioms (\S+)', query.read_text(), re.M)
    if not expected:
        raise SystemExit(f'FAIL: empty query {query.name}')
    result = subprocess.run([LAKE, 'env', 'lean', str(query)], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    query.with_suffix('.log').write_text(result.stdout)
    if result.returncode:
        raise SystemExit(f'FAIL: {query.name}\n{result.stdout}')
    validate(result.stdout, expected)
    print(f'PASS: {query.name}', flush=True)
print('All interface allowlists and parser negative controls passed', flush=True)
