#!/usr/bin/env python3
"""Build the article with Tectonic, then run the PDF-level audit."""
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
    parser.add_argument("--offline", action="store_true", help="use an already seeded Tectonic cache")
    args = parser.parse_args()
    tectonic = os.environ.get("TECTONIC") or shutil.which("tectonic")
    fallback = Path(r"D:\Anaconda\envs\latex\Library\bin\tectonic.exe")
    if not tectonic and fallback.is_file():
        tectonic = str(fallback)
    if not tectonic:
        print("missing Tectonic; set TECTONIC or add it to PATH", file=sys.stderr)
        return 2
    env = dict(os.environ)
    local_cache = Path(os.environ.get("LOCALAPPDATA", str(Path.home()))) / "Tectonic"
    env["TECTONIC_CACHE_DIR"] = env.get("TECTONIC_CACHE_DIR", str(local_cache))
    env["SOURCE_DATE_EPOCH"] = "1794441600"
    out = ROOT / "build"
    out.mkdir(exist_ok=True)
    for path in out.glob("main.*"):
        path.unlink()
    cmd = [tectonic, "--keep-logs", "--outdir", str(out), "main.tex"]
    if args.offline:
        cmd.insert(1, "-C")
    result = subprocess.run(cmd, cwd=ROOT, env=env)
    pdf = out / "main.pdf"
    if result.returncode or not pdf.is_file():
        return 1
    log_path = out / "main.log"
    log = log_path.read_text(encoding="utf-8", errors="strict") if log_path.exists() else ""
    if re.search(r"Overfull|Missing character|undefined reference|Citation .* undefined", log, re.I):
        print("BUILD FAILED: TeX layout, font or reference warning", file=sys.stderr)
        return 1
    shutil.copy2(pdf, ROOT / "periodic_gaussian_dimensional_sweep.pdf")
    audit = subprocess.run([sys.executable, "audit/audit.py"], cwd=ROOT)
    return audit.returncode


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except Exception as exc:
        print(f"BUILD ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
