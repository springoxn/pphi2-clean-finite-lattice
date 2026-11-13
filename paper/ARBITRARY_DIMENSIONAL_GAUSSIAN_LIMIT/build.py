#!/usr/bin/env python3
"""Build the standalone article and run its fail-closed audit."""
from __future__ import annotations
import os, re, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def main() -> int:
    tectonic = os.environ.get("TECTONIC") or shutil.which("tectonic")
    fallback = Path(r"D:\Anaconda\envs\latex\Library\bin\tectonic.exe")
    if not tectonic and fallback.is_file():
        tectonic = str(fallback)
    if not tectonic:
        print("missing Tectonic", file=sys.stderr)
        return 2
    out = ROOT / "build"
    out.mkdir(exist_ok=True)
    for p in out.glob("main.*"):
        p.unlink()
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = "1794441600"
    env["PYTHONIOENCODING"] = "utf-8"
    cmd = [tectonic, "--keep-logs", "--outdir", str(out), "main.tex"]
    proc = subprocess.run(cmd, cwd=ROOT, env=env)
    if proc.returncode:
        return 1
    log = (out / "main.log").read_text(encoding="utf-8") if (out / "main.log").exists() else ""
    bad = re.findall(r"Missing character|undefined reference|Citation .* undefined|There were undefined", log, re.I)
    if bad:
        print("TeX diagnostics rejected: " + ", ".join(sorted(set(bad))), file=sys.stderr)
        return 1
    pdf = out / "main.pdf"
    if not pdf.is_file():
        return 1
    shutil.copyfile(pdf, ROOT / "main.pdf")
    return subprocess.run([sys.executable, "audit/audit.py"], cwd=ROOT).returncode

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"BUILD ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
