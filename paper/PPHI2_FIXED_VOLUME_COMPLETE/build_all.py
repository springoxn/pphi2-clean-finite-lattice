#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Single build entry point for the fixed-volume weak-limit paper.

    python build_all.py [--check-only] [--skip-audit] [--no-compile]

Steps, each of which stops the chain on failure:

  1. regenerate the counts                  audit/count_lean.py  -> generated/metrics.tex
  2. regenerate the ledger and transcript    audit/make_ledger.py -> generated/{ledger,axioms}.tex
  3. run the gate's own negative controls    audit/verify_paper.py --self-test
  4. run the gate                            audit/verify_paper.py
  5. compile with Tectonic, project-local cache, offline if the cache is seeded
  6. verify the PDF was written by THIS run and is newer than every source
  7. stamp build/LAST_BUILD.txt with the hash of every source and of the output

Why a single entry point: a partially successful manual sequence can leave a
stale main.pdf that still looks fine, because a PDF cannot tell you which
sources produced it.  The stamp records the hash of every source.

The script never writes into a .tex source.  generated/*.tex are derived
artefacts and are rewritten on every run, by design.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding="utf-8", errors="replace")

HERE = Path(__file__).resolve().parent
PDF_NAME = "pphi2_fixed_volume_weak_limit_complete.pdf"

TECTONIC_CANDIDATES = (
    os.environ.get("TECTONIC"),
    r"D:\Anaconda\envs\latex\Library\bin\tectonic.exe",
    shutil.which("tectonic"),
)

CACHE_SEED = HERE.parent.parent / "paper" / "PPHI2_FINITE_LATTICE" / ".texcache"

# Any overfull box is a defect here: the paper's long Lean identifiers either sit in
# a table column (where the column is sized to the name) or carry explicit break
# points, so a box that overflows means a name escaped both treatments.
MAX_OVERFULL = 0


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def sources():
    out = [HERE / "main.tex", HERE / "refs.bib",
           HERE / "ext" / "axiom_transcript.txt"]
    out += sorted((HERE / "sections").glob("*.tex"))
    out += sorted((HERE / "figures").glob("*.tex"))
    out += sorted((HERE / "generated").glob("*.tex"))
    out += sorted((HERE / "figures").glob("*.png"))
    out += sorted((HERE / "audit").glob("*.py"))
    return [p for p in out if p.exists()]


OVERFULL = re.compile(r"Overfull \\hbox \(([0-9.]+)pt too wide\)")
UNDEFINED = re.compile(r"(?:Reference|Citation) `[^']*' on page \d+ undefined")


def scan_log(log: Path):
    """Report the two log defects that a green exit code does not catch.

    Tectonic exits 0 on an overfull box and on an undefined reference: both are
    warnings to the engine and visible defects to the reader.  The 2026-11-03
    audit found eight overfull boxes in a build that reported success, the worst
    of them pushing a declaration name through the page edge, so these two counts
    are part of the gate now rather than something a human greps for.
    """
    if not log.exists():
        return None
    text = log.read_text(encoding="utf-8", errors="replace")
    boxes = [float(m.group(1)) for m in OVERFULL.finditer(text)]
    undefined = len(UNDEFINED.findall(text))
    return {"overfull": len(boxes), "worst": max(boxes) if boxes else 0.0,
            "undefined": undefined}


def run(cmd, **kw):
    print(">> " + " ".join(str(c) for c in cmd))
    return subprocess.run([str(c) for c in cmd], **kw)


def find_tectonic() -> Path | None:
    for c in TECTONIC_CANDIDATES:
        if c and Path(c).exists():
            return Path(c)
    return None


def seed_cache(cache: Path):
    if cache.exists() and any(cache.iterdir()):
        return
    if CACHE_SEED.exists():
        cache.mkdir(parents=True, exist_ok=True)
        for item in CACHE_SEED.iterdir():
            dst = cache / item.name
            if item.is_dir():
                shutil.copytree(item, dst, dirs_exist_ok=True)
            else:
                shutil.copy2(item, dst)
        print("    seeded Tectonic cache from %s" % CACHE_SEED)
    else:
        print("    !! no Tectonic cache to seed from; the build will need network")


def main(argv) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check-only", action="store_true", help="steps 1-4 only")
    ap.add_argument("--skip-audit", action="store_true", help="skip steps 1-4")
    ap.add_argument("--no-compile", action="store_true", help="steps 1-4 and stop")
    args = ap.parse_args(argv)

    t0 = time.time()
    py = sys.executable

    if not args.skip_audit:
        for step in (["audit/count_lean.py"], ["audit/make_ledger.py"],
                     ["audit/make_bib.py"],
                     ["audit/verify_paper.py", "--self-test"],
                     ["audit/verify_paper.py"]):
            r = run([py] + step, cwd=HERE)
            if r.returncode != 0:
                print("BUILD FAILED at %s" % step[0])
                return r.returncode
    if args.check_only or args.no_compile:
        print("checks passed in %.1fs (no compile requested)" % (time.time() - t0))
        return 0

    tect = find_tectonic()
    if tect is None:
        print("PREFLIGHT FAIL: tectonic not found; tried %s" % (TECTONIC_CANDIDATES,))
        return 2

    cache = HERE / ".texcache"
    seed_cache(cache)
    env = dict(os.environ)
    env["TECTONIC_CACHE_DIR"] = str(cache)
    # an offline cache is enough; if it is incomplete Tectonic needs a route out
    for var in ("HTTP_PROXY", "HTTPS_PROXY"):
        env.setdefault(var, "http://127.0.0.1:7890")

    build = HERE / "build"
    build.mkdir(exist_ok=True)
    pdf = HERE / "main.pdf"
    if pdf.exists():
        pdf.unlink()

    r = run([tect, "-C", "--keep-logs", "--outdir", str(build), "main.tex"],
            cwd=HERE, env=env)
    produced = build / "main.pdf"
    if r.returncode != 0 or not produced.exists():
        print("BUILD FAILED: tectonic exit %s, pdf present=%s" % (r.returncode, produced.exists()))
        return 1

    newest = max(sources(), key=lambda p: p.stat().st_mtime)
    if produced.stat().st_mtime < newest.stat().st_mtime:
        print("BUILD FAILED: main.pdf is older than %s" % newest)
        return 1

    # A green exit code says nothing about the two reader-visible log defects.
    logstat = scan_log(build / "main.log")
    if logstat is None:
        print("BUILD FAILED: no main.log to scan")
        return 1
    print("log: overfull %d (worst %.2fpt), undefined %d"
          % (logstat["overfull"], logstat["worst"], logstat["undefined"]))
    if logstat["overfull"] > MAX_OVERFULL or logstat["undefined"] > 0:
        print("BUILD FAILED: log defects (overfull > %d or undefined references)"
              % MAX_OVERFULL)
        return 1

    shutil.copy2(produced, pdf)
    shutil.copy2(produced, HERE / PDF_NAME)

    stamp = build / "LAST_BUILD.txt"
    lines = ["# build stamp for paper/PPHI2_FIXED_VOLUME_COMPLETE",
             "utc        %s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
             "seconds    %.1f" % (time.time() - t0),
             "tectonic   %s" % tect,
             "log        overfull %d (worst %.2fpt), undefined %d"
             % (logstat["overfull"], logstat["worst"], logstat["undefined"]),
             "pdf        %s  %d bytes  sha256=%s" % (PDF_NAME, produced.stat().st_size, sha256(produced)),
             "sources"]
    for p in sources():
        lines.append("  %-46s %s" % (p.relative_to(HERE).as_posix(), sha256(p)))
    stamp.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print("BUILD OK: %s (%d bytes)" % (pdf, produced.stat().st_size))
    print("stamp: %s" % stamp)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
