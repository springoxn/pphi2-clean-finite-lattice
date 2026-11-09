#!/usr/bin/env python3
"""Portable Tectonic build; --offline requires a seeded Tectonic cache.
Set TECTONIC to a compiler executable and TECTONIC_CACHE_DIR to a cache, or
put tectonic on PATH. Python audits require sympy and PyMuPDF.
"""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--offline', action='store_true')
    args = parser.parse_args()
    tectonic = os.environ.get('TECTONIC') or shutil.which('tectonic')
    local = Path(r'D:\Anaconda\envs\latex\Library\bin\tectonic.exe')
    if not tectonic and local.is_file():
        tectonic = str(local)
    if not tectonic:
        print('missing Tectonic: set TECTONIC or put tectonic on PATH', file=sys.stderr)
        return 2
    env = dict(os.environ)
    cache = Path(env.get('TECTONIC_CACHE_DIR', str(ROOT / '.texcache')))
    seed = ROOT.parent / 'PPHI2_FIXED_VOLUME_COMPLETE' / '.texcache'
    if not cache.exists() and seed.exists():
        shutil.copytree(seed, cache)
    env['TECTONIC_CACHE_DIR'] = str(cache)
    env['SOURCE_DATE_EPOCH'] = '1793664000'
    output = ROOT / 'build'
    output.mkdir(exist_ok=True)
    for path in output.glob('main.*'):
        path.unlink()
    cmd = [tectonic, '--keep-logs', '--outdir', str(output), 'main.tex']
    if args.offline:
        cmd.insert(1, '-C')
    proc = subprocess.run(cmd, cwd=ROOT, env=env)
    pdf = output / 'main.pdf'
    if proc.returncode or not pdf.is_file():
        return 1
    text = (output / 'main.log').read_text(encoding='utf-8')
    if re.search(r'Overfull|undefined|Missing character', text, re.I):
        print('BUILD FAILED: layout, reference or font defect', file=sys.stderr)
        return 1
    audit = subprocess.run([sys.executable, 'audit/audit.py', '--pdf', str(pdf)], cwd=ROOT)
    if audit.returncode:
        return audit.returncode
    shutil.copy2(pdf, ROOT / 'periodic_gaussian_dimension_bridge.pdf')
    print('BUILD OK: periodic_gaussian_dimension_bridge.pdf')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
