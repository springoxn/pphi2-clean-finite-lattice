#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Portable verification for this repository.  Standard library only.

    python verify.py            # every published file against MANIFEST.sha256
    python verify.py --count    # the counts claimed in README.md, recomputed
    python verify.py --lean     # additionally re-run the axiom gates (needs lake)
    python verify.py --ext      # the post-pin extension: hashes, coverage, axioms
    python verify.py --all      # manifest + counts + extension + gates

Why: the claims of this repository are claims about *bytes* and about *Lean
declarations*.  A reader should not have to trust the prose: the manifest can be
checked anywhere, the counts are functions of the sources, and the axiom gates
are the scripts the authors used, made portable.

Exit codes: 0 all requested checks passed, 1 an assertion failed, 2 the tool
could not run (missing file, missing toolchain).

Known limits: the manifest proves that the tree is the one that was published,
not that it is correct; --lean re-runs the gates but not a full `lake build`
(that needs Mathlib and takes a long time -- see README).
"""
from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "MANIFEST.sha256"
SKIP_DIRS = {".git", ".lake", "build", "__pycache__"}
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+"
    r"([^\s:({\[]+)")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def walk() -> list[Path]:
    out = []
    for p in sorted(ROOT.rglob("*")):
        if p.is_dir():
            continue
        if SKIP_DIRS & set(p.relative_to(ROOT).parts):
            continue
        out.append(p)
    return out


def strip_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    n = len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def check_manifest() -> tuple[bool, str]:
    if not MANIFEST.exists():
        return False, "MANIFEST.sha256 is missing"
    entries = {}
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        digest, rel = line.split(None, 1)
        entries[rel.strip()] = digest
    bad, missing = [], []
    for rel, digest in entries.items():
        p = ROOT / rel
        if not p.exists():
            missing.append(rel)
        elif sha256(p) != digest:
            bad.append(rel)
    listed = set(entries)
    extra = [str(p.relative_to(ROOT)).replace("\\", "/")
             for p in walk()
             if str(p.relative_to(ROOT)).replace("\\", "/") not in listed
             and p.name not in ("MANIFEST.sha256",)]
    problems = []
    if missing:
        problems.append("%d missing: %s" % (len(missing), ", ".join(missing[:5])))
    if bad:
        problems.append("%d modified: %s" % (len(bad), ", ".join(bad[:5])))
    if extra:
        problems.append("%d unlisted: %s" % (len(extra), ", ".join(extra[:5])))
    if problems:
        return False, "; ".join(problems)
    return True, "%d files verified against MANIFEST.sha256" % len(entries)


def extension_modules() -> set[str]:
    """The post-pin modules, as named by the evidence transcript itself."""
    log = ROOT / "docs" / "extension_evidence.log"
    if not log.exists():
        return set()
    out = set()
    for line in log.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^source_sha256 [0-9a-f]{64} (\S+)$", line.strip())
        if m:
            out.add(m.group(1))
    return out


def _census(files: list[Path]) -> tuple[int, int, int]:
    """(lines, declarations, sorry occurrences) over a list of Lean files."""
    counts = 0
    lines = sorry = 0
    for f in files:
        raw = f.read_text(encoding="utf-8")
        lines += raw.count("\n")
        body = strip_comments(raw)
        for line in body.splitlines():
            if DECL.match(line):
                counts += 1
        sorry += len(re.findall(r"\bsorry\b", body))
    return lines, counts, sorry


def check_counts() -> tuple[bool, str]:
    core = sorted((ROOT / "AImathPPhi2Clean").glob("*.lean"))
    ext_rel = extension_modules()
    ext = [p for p in core if str(p.relative_to(ROOT)).replace("\\", "/") in ext_rel]
    arch = [p for p in core if p not in ext]
    root_mod = ROOT / "AImathPPhi2Clean.lean"

    counts = {k: 0 for k in ("theorem", "lemma", "def", "abbrev", "structure",
                             "instance", "class", "inductive")}
    axioms = 0
    for f in core + ([root_mod] if root_mod.exists() else []):
        body = strip_comments(f.read_text(encoding="utf-8"))
        for line in body.splitlines():
            m = DECL.match(line)
            if m:
                counts[m.group(1)] += 1
        axioms += len(re.findall(r"(?m)^\s*axiom\s", body))

    def count_in(glob: str, pattern: str) -> int:
        n = 0
        for p in ROOT.glob(glob):
            n += len(re.findall(pattern, p.read_text(encoding="utf-8"), re.M))
        return n

    declared = count_in("audit/finite_lattice_all_declarations_interface.lean",
                        r"^#print axioms ")
    interfaces = len(list((ROOT / "audit").glob("*_interface.lean")))
    build = (ROOT / "audit" / "finite_lattice_build.log").read_text(encoding="utf-8")
    m = re.search(r"Build completed successfully \((\d+) jobs\)", build)
    jobs = int(m.group(1)) if m else -1
    decls = sum(counts.values())
    thm = counts["theorem"] + counts["lemma"]

    a_lines, a_decls, a_sorry = _census(arch)
    e_lines, e_decls, e_sorry = _census(ext)
    print("  archive core            %d modules, %d lines, %d declarations"
          % (len(arch), a_lines, a_decls))
    print("  library root            %d lines (the archive's root + the %d "
          "extension imports)" % (root_mod.read_text(encoding="utf-8").count("\n"),
                                  len(ext)))
    print("  post-pin extension      %d modules, %d lines, %d declarations"
          % (len(ext), e_lines, e_decls))
    print("  whole package           %d modules, %d declarations (theorem-level %d)"
          % (len(core), decls, thm))
    print("  sorry occurrences       %d" % (a_sorry + e_sorry))
    print("  axiom declarations      %d" % axioms)
    print("  axiom report queries    %d (archive)" % declared)
    print("  interface certificates  %d" % interfaces)
    print("  archived build jobs     %d" % jobs)
    if a_sorry or e_sorry or axioms:
        return False, ("found %d sorry and %d axiom declarations"
                       % (a_sorry + e_sorry, axioms))
    return True, "sources are free of `sorry` and of `axiom` declarations"


ALLOW = re.compile(r"ALLOW = \{([^}]*)\}")


def check_extension() -> tuple[bool, str]:
    """The post-pin step: same bytes, same declarations, same allowlist.

    What this establishes: the two extension modules are the ones the published
    evidence transcript describes (by hash), the library root is the root that
    run built (by hash and by import), every declaration they introduce has an
    axiom report, and every reported footprint is inside the archive's allowlist.
    What it does not: that the statements are the intended ones, and that no
    other corruption of the transcript exists.
    """
    log = ROOT / "docs" / "extension_evidence.log"
    if not log.exists():
        return False, "docs/extension_evidence.log is missing"
    text = log.read_text(encoding="utf-8")
    meta: dict[str, str] = {}
    for line in text.splitlines():
        m = re.match(r"^([a-z0-9_]+): (.*)$", line.strip())
        if m:
            meta.setdefault(m.group(1), m.group(2))
    recorded = {m.group(2): m.group(1) for m in
                re.finditer(r"(?m)^source_sha256 ([0-9a-f]{64}) (\S+)$", text)}
    reports = {}
    for m in re.finditer(r"(?m)^axioms (\S+) :: (.*)$", text):
        body = m.group(2).strip()
        reports[m.group(1).split(".")[-1]] = (
            [] if body in ("", "-") else [t.strip() for t in body.split(",") if t.strip()])
    if not recorded:
        return False, "the transcript records no module hashes"

    problems = []
    for rel, digest in recorded.items():
        p = ROOT / rel
        if not p.exists():
            problems.append("missing %s" % rel)
        elif sha256(p) != digest:
            problems.append("hash mismatch for %s" % rel)
    root_mod = ROOT / "AImathPPhi2Clean.lean"
    root_text = root_mod.read_text(encoding="utf-8")
    for rel in recorded:
        name = rel[:-5].replace("/", ".")
        if not re.search(r"(?m)^import %s$" % re.escape(name), root_text):
            problems.append("the library root does not import %s" % name)
    if meta.get("root_sha256_at_run") != sha256(root_mod):
        problems.append("the published root is not the root the evidence run built")

    declared = []
    for rel in recorded:
        body = strip_comments((ROOT / rel).read_text(encoding="utf-8"))
        declared += [m.group(2) for line in body.splitlines()
                     if (m := DECL.match(line)) and m.group(2) != "_"]
    missing = [n for n in declared if n not in reports]
    if missing:
        problems.append("%d declaration(s) without an axiom report: %s"
                        % (len(missing), ", ".join(missing[:4])))
    gate = ROOT / "audit" / "run_interface_gate.py"
    allow = set()
    if gate.exists():
        found = ALLOW.findall(gate.read_text(encoding="utf-8"))
        if found:
            allow = {a.strip().strip("'\"") for a in found[0].split(",")}
    outside = {n: ax for n, ax in reports.items() if not set(ax) <= allow}
    if outside:
        problems.append("footprint outside the allowlist: %s" % ", ".join(sorted(outside)))
    if problems:
        return False, "; ".join(problems)
    return True, ("%d modules, %d declarations, %d clean footprints, root == the "
                  "built root" % (len(recorded), len(declared), len(reports)))


def check_lean() -> tuple[bool, str]:
    lake = (shutil.which("lake")
            or str(Path.home() / ".elan" / "toolchains"
                   / "leanprover--lean4---v4.34.0-rc2" / "bin" / "lake"))
    if not Path(lake).exists() and not shutil.which(lake):
        # a missing toolchain is a tool error (exit 2), not a failed assertion
        raise RuntimeError("no `lake` found: set LAKE, or install the pinned "
                           "toolchain (see lean-toolchain)")
    env = dict(**__import__("os").environ, LAKE=lake)
    py = shutil.which("python3") or sys.executable
    for script in ("audit/run_firewall.sh", "audit/run_interface_gate.py"):
        cmd = (["bash", str(ROOT / script)] if script.endswith(".sh")
               else [py, str(ROOT / script)])
        r = subprocess.run(cmd, cwd=str(ROOT), env=env, capture_output=True,
                           text=True, encoding="utf-8", errors="replace")
        tail = (r.stdout or "").strip().splitlines()[-1:] or [""]
        print("  %-32s exit %d  %s" % (script, r.returncode, tail[0][:90]))
        if r.returncode != 0:
            return False, "%s failed" % script
    return True, "axiom firewall and interface gate both passed"


def main() -> int:
    args = sys.argv[1:]
    explicit = {"--manifest", "--count", "--lean", "--ext"} & set(args)
    do_all = "--all" in args
    checks = []
    if do_all or "--count" in args:
        checks.append(("counts", check_counts))
    if do_all or "--ext" in args:
        checks.append(("extension", check_extension))
    if do_all or "--lean" in args:
        checks.append(("lean gates", check_lean))
    if do_all or "--manifest" in args or not explicit:
        checks.append(("manifest", check_manifest))

    failed = 0
    for name, fn in checks:
        try:
            ok, msg = fn()
        except Exception as exc:  # tool error
            print("ERROR %-12s %r" % (name, exc))
            return 2
        print("%s %-12s %s" % ("PASS" if ok else "FAIL", name, msg))
        failed += 0 if ok else 1
    if failed:
        print("%d check(s) failed" % failed)
        return 1
    print("all requested checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
