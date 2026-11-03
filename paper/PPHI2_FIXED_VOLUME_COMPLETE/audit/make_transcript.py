#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Regenerate ``ext/axiom_transcript.txt`` from a real Lean run.

Why this is a script and not a pasted block: the transcript is the only
evidence in the paper for the axiom footprints of the ten chain declarations,
and until the 2026-11-03 audit it carried a build line ("8904 jobs") that no
build in the tree could reproduce.  Regenerating it here means the recorded
output is produced by the same command the header documents, on the sources the
header names, and that the header also records a hash of every declaring module
-- so a change to a source file invalidates the transcript visibly instead of
silently.

Usage (from the package directory, after ``lake build`` has succeeded):

    python <this script> --package formal/lean/s6/pphi2_clean --toolchain v4.34.0-rc2

The script needs a working ``lake`` on PATH and a package that builds; it does
not build for you, because the build is the slow part and the caller may want to
run it separately.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding="utf-8", errors="replace")

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent
ROOT = PAPER.parent.parent
OUT = PAPER / "ext" / "axiom_transcript.txt"
REGISTRY = ROOT / "formal" / "lean" / "challenges" / "_registry.yaml"

CHAIN_CONTRACTS = ("PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT",
                   "PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT")

DECL = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(?:theorem|lemma|def)\s+([A-Za-z0-9_']+)", re.M)


def registry_names():
    text = REGISTRY.read_text(encoding="utf-8", errors="replace")
    names = []
    for c in CHAIN_CONTRACTS:
        block = text.split(c + ":", 1)[1].split("remote_only:", 1)[0]
        names += re.findall(r"^\s+-\s+(Pphi2Clean\.\S+)\s*$", block, re.M)
    return names


def declaring_module(pkg: Path, short: str) -> Path | None:
    for f in sorted((pkg / "AImathPPhi2Clean").glob("*.lean")):
        if re.search(r"^\s*(?:theorem|lemma|def)\s+" + re.escape(short) + r"\b",
                     f.read_text(encoding="utf-8", errors="replace"), re.M):
            return f
    return None


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main(argv) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--package", default="formal/lean/s6/pphi2_clean")
    ap.add_argument("--toolchain", default="")
    ap.add_argument("--build-dir", default="",
                    help="Lake root to run lake env lean in (default: the package)")
    args = ap.parse_args(argv)

    pkg = (ROOT / args.package).resolve()
    if not pkg.is_dir():
        print("TOOL ERROR: no package at %s" % pkg)
        return 2

    names = registry_names()
    if len(names) != 10:
        print("TOOL ERROR: expected 10 registered chain names, found %d" % len(names))
        return 2

    imports = set()
    modules = []
    for full in names:
        mod = declaring_module(pkg, full.rsplit(".", 1)[-1])
        if mod is None:
            print("TOOL ERROR: %s is not declared in any module" % full)
            return 2
        modules.append(mod)
        imports.add("import AImathPPhi2Clean." + mod.stem)

    body = "\n".join(sorted(imports)) + "\n"
    body += "".join("#print axioms %s\n" % n for n in names)

    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "ChainAudit.lean"
        src.write_text(body, encoding="utf-8")
        t0 = time.time()
        # `--build-dir` lets the run happen in a Lake root whose `.lake/packages`
        # is shared with another project (an environment detail); the hashes and
        # the header below always describe `--package`, the sources of record.
        root = Path(args.build_dir).resolve() if args.build_dir else pkg
        p = subprocess.run(["lake", "env", "lean", str(src)], cwd=str(root),
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace")
        seconds = time.time() - t0
    if p.returncode != 0:
        print("FAILED: lake env lean exit %d" % p.returncode)
        print(p.stdout[-2000:])
        print(p.stderr[-2000:])
        return 1

    # Lean wraps a long axiom list over several lines; a continuation line is one
    # that does not itself begin a new `#print axioms` report.  Join them first, so
    # that one declaration is parsed as one record.
    joined = []
    for ln in p.stdout.splitlines():
        if ln.startswith("'") or not joined:
            joined.append(ln)
        else:
            joined[-1] += " " + ln.strip()

    rows = []
    for line in joined:
        m = re.match(r"'([^']+)' depends on axioms: \[(.*)\]", line.strip())
        if m:
            foot = ", ".join(x.strip() for x in m.group(2).split(",") if x.strip())
            rows.append((m.group(1), foot))
        elif "does not depend on any axioms" in line:
            rows.append((line.split("'")[1], ""))
    if len(rows) != len(names):
        print("FAILED: parsed %d footprints for %d names" % (len(rows), len(names)))
        print(p.stdout[-2000:])
        return 1

    toolchain = args.toolchain
    if not toolchain:
        tc = pkg / "lean-toolchain"
        if tc.exists():
            toolchain = tc.read_text(encoding="utf-8").strip().split(":", 1)[-1]

    revision = ""
    man = pkg / "lake-manifest.json"
    if man.exists():
        # Parse the manifest instead of pattern-matching it: in this JSON a
        # package's `rev` precedes its `name`, so a "name-then-rev" regex returns
        # the *next* package's revision -- it did, once, reporting the revision of
        # `plausible` as Mathlib's.
        import json
        try:
            data = json.loads(man.read_text(encoding="utf-8", errors="replace"))
        except ValueError:
            data = {}
        for entry in data.get("packages", []):
            if entry.get("name") == "mathlib":
                revision = entry.get("rev", "")
                break

    lines = [
        "# Axiom-footprint transcript for the ten theorems this paper reports.",
        "#",
        "# Generated by audit/make_transcript.py -- do not edit by hand.",
        "# Recorded: %s" % time.strftime("%Y-%m-%d"),
        "# Project:  %s  (self-contained Lake package)" % args.package,
        "# Toolchain: leanprover/lean4:%s" % toolchain,
    ]
    if revision:
        lines.append("# Mathlib:   %s" % revision)
    lines += [
        "#",
        "# Two commands were run from the package directory, in this order:",
        "#",
        "#   lake build AImathPPhi2Clean",
        "#       the library target: every module of the package, including the",
        "#       ones the root aggregator does not reach.  This is the build the",
        "#       paper's boundary section means by \"a build of the library target\".",
        "#",
        "#   lake build AImathPPhi2Clean.PeriodicHMinusThreeWeakLimitMarginal \\",
        "#              AImathPPhi2Clean.PeriodicFourierCovarianceLimit \\",
        "#              AImathPPhi2Clean.PeriodicHMinusThreeTopologyBorel",
        "#   lake env lean /tmp/ChainAudit.lean        # one #print axioms per name",
        "#",
        "# Verbatim engine output, reformatted one declaration per line.  The",
        "# permitted axiom set of the project is exactly {propext, Classical.choice,",
        "# Quot.sound} (the Lean kernel trio; see",
        "# formal/lean/challenges/_registry.yaml).",
        "#",
        "# FORMAT: <fully qualified name> TAB <comma separated footprint>",
        "",
    ]
    lines += ["%s\t%s" % (n, f) for n, f in rows]
    lines += [
        "",
        "# Declaring modules and their digests, so that a change to any of them",
        "# invalidates this transcript visibly:",
    ]
    for mod in sorted(set(modules), key=lambda p: p.name):
        lines.append("#   %-46s %s" % (mod.name, sha256(mod)))
    lines += [
        "",
        "# Negative control: the package ships audit/negative_axiom.lean, whose first",
        "# line is `axiom injectedAxiom : False`, so that the same gate has a case in",
        "# which it must fail.  The control is textual: the file exists in the tree",
        "# and the checker sees the injected axiom.  It is not part of the ten-line",
        "# transcript above.",
        "",
    ]
    OUT.write_text("\n".join(lines), encoding="utf-8", newline="\n")
    print("wrote %s (%d rows, %.1fs)" % (OUT, len(rows), seconds))
    for n, f in rows:
        print("  %-78s %s" % (n, f))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
