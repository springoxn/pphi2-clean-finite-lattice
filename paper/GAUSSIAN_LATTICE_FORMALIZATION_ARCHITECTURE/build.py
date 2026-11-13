#!/usr/bin/env python3
"""Build twice, compare PDF bytes, then audit the standalone article."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    engine = os.environ.get('TECTONIC') or shutil.which('tectonic')
    fallback = Path(r'D:\Anaconda\envs\latex\Library\bin\tectonic.exe')
    if not engine and fallback.is_file():
        engine = str(fallback)
    if not engine:
        raise RuntimeError('Install Tectonic or set TECTONIC')
    env = dict(os.environ, SOURCE_DATE_EPOCH='1794528000', PYTHONIOENCODING='utf-8')
    pdfs = []
    for run in ('first', 'second'):
        out = ROOT / 'build' / run
        out.mkdir(parents=True, exist_ok=True)
        proc = subprocess.run([engine, '--keep-logs', '--outdir', str(out), 'main.tex'],
                              cwd=ROOT, env=env)
        if proc.returncode:
            return 1
        log = (out / 'main.log').read_text(encoding='utf-8')
        if re.search(r'Missing character|undefined reference|Citation .* undefined|There were undefined', log, re.I):
            raise AssertionError('Unresolved references or missing glyphs')
        pdfs.append((out / 'main.pdf').read_bytes())
    if pdfs[0] != pdfs[1]:
        raise AssertionError('PDF builds differ byte for byte')
    shutil.copyfile(ROOT / 'build/second/main.pdf', ROOT / 'main.pdf')
    return subprocess.run([sys.executable, 'audit/audit.py'], cwd=ROOT, env=env).returncode


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as exc:
        print('BUILD ERROR:', exc, file=sys.stderr)
        sys.exit(2)
