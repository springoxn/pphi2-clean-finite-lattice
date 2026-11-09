#!/usr/bin/env python3
"""Mutation controls: the article checker must reject source and contract drift."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix='bridge-audit-') as name:
        root = Path(name)
        for filename in ('main.tex', 'bibliography.tex'):
            shutil.copy2(ROOT / filename, root / filename)
        shutil.copytree(ROOT / 'sections', root / 'sections')
        shutil.copytree(ROOT / 'audit', root / 'audit', ignore=shutil.ignore_patterns('__pycache__'))
        def run(expected):
            with (root / 'control.log').open('w', encoding='utf-8') as log:
                result = subprocess.run([sys.executable, str(root / 'audit/audit.py'), '--source-only'],
                                        stdout=log, stderr=subprocess.STDOUT)
            if result.returncode != expected:
                print((root / 'control.log').read_text(encoding='utf-8'))
                raise ValueError(f'expected {expected}, got {result.returncode}')
        run(0)
        source = root / 'sections/introduction.tex'
        original = source.read_bytes()
        source.write_bytes(original.replace(b'Common paper theorem', b'Altered theorem'))
        run(1)
        print('PASS negative control: missing theorem anchor')
        source.write_bytes(original)
        contract = root / 'audit/bridge_contract.log'
        original = contract.read_bytes()
        contract.write_bytes(original.replace(b'Quot.sound', b'customAssumption'))
        run(1)
        print('PASS negative control: altered Lean transcript')
        contract.write_bytes(original)
        run(0)
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
