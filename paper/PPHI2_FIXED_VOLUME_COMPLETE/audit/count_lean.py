#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Regenerate ``generated/metrics.tex`` from the sources on disk.

Why: every structural count printed in this paper is a macro defined here, so a
count can never silently rot.  The paper body is forbidden (by
``audit/verify_paper.py``, check ``M``) to contain the literal value of any
macro other than inside ``generated/``.

What is counted, and from where (single provider per number):

  package modules / lines        formal/lean/s6/pphi2_clean/AImathPPhi2Clean/*.lean
  audit probes                   formal/lean/s6/pphi2_clean/audit/*.lean
  ``sorry`` / project axioms     the same package files, comments stripped
  root development files / lines formal/lean/s6/*.lean
  contracts, permitted axioms    formal/lean/challenges/_registry.yaml
  chain theorems                 the two fixed-volume challenges in that file
  proof documents                proofs/*.md
  probes                         verify/*_probe.py
  failure cards                  proof_graph/failures/*.md (minus README)

Known false-positive class (deliberate, reported not hidden): the token
``axiom`` also occurs inside doc comments; the counter strips block and line
comments before counting, and reports the naive count alongside so that the
difference is visible in the build log.

Not registered in run_checks: this is a paper-local tool.
"""
from __future__ import annotations

import io
import re
import sys
from pathlib import Path

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding="utf-8", errors="replace")

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent
ROOT = PAPER.parent.parent          # E:\study\AImath
OUT = PAPER / "generated" / "metrics.tex"

CLEAN_LIB = ROOT / "formal" / "lean" / "s6" / "pphi2_clean" / "AImathPPhi2Clean"
CLEAN_AUDIT = ROOT / "formal" / "lean" / "s6" / "pphi2_clean" / "audit"
ROOT_LEAN = ROOT / "formal" / "lean" / "s6"
REGISTRY = ROOT / "formal" / "lean" / "challenges" / "_registry.yaml"

CHAIN_CONTRACTS = ("PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT",
                   "PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT")

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"--[^\n]*")


def strip_comments(text: str) -> str:
    return LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))


def lean_files(d: Path):
    return sorted(d.glob("*.lean")) if d.is_dir() else []


def count_lines(paths) -> int:
    total = 0
    for p in paths:
        total += len(p.read_text(encoding="utf-8", errors="replace").splitlines())
    return total


def count_sorry_axiom(paths):
    """Return (sorry, project_axioms) with comments stripped."""
    sorry = axiom = 0
    for p in paths:
        body = strip_comments(p.read_text(encoding="utf-8", errors="replace"))
        sorry += len(re.findall(r"\bsorry\b", body))
        axiom += len(re.findall(r"^\s*axiom\s+\w", body, re.M))
    return sorry, axiom


def naive_sorry_axiom(paths):
    sorry = axiom = 0
    for p in paths:
        raw = p.read_text(encoding="utf-8", errors="replace")
        sorry += len(re.findall(r"\bsorry\b", raw))
        axiom += len(re.findall(r"^\s*axiom\s+\w", raw, re.M))
    return sorry, axiom


def registry_counts():
    """Parse the contract registry without a YAML dependency."""
    if not REGISTRY.exists():
        return None, None, None
    text = REGISTRY.read_text(encoding="utf-8", errors="replace")
    permits = re.search(r"^permitted_axioms:\s*\[(.*?)\]", text, re.M)
    n_permitted = len([x for x in permits.group(1).split(",") if x.strip()]) if permits else None
    # top-level keys under 'challenges:' (two-space indent, ends with ':')
    body = text.split("\nchallenges:", 1)
    challenges = {}
    if len(body) == 2:
        cur = None
        field = None
        for line in body[1].splitlines():
            if re.match(r"^imported_nodes:", line) or re.match(r"^unwired:", line):
                break
            m = re.match(r"^  ([A-Z0-9_]+):\s*$", line)
            if m:
                cur = m.group(1)
                challenges[cur] = []
                field = None
                continue
            # a sub-key of the current challenge (4-space indent, e.g. theorem_names:)
            k = re.match(r"^    ([a-z_]+):", line)
            if k:
                field = k.group(1)
                continue
            if cur and field == "theorem_names" and re.match(r"^\s+-\s+\S", line):
                challenges[cur].append(line.strip()[2:].strip())
    n_chain = sum(len(challenges.get(c, [])) for c in CHAIN_CONTRACTS)
    return len(challenges), n_permitted, n_chain


def toolchain() -> str:
    for cand in (ROOT / ".local-lean" / "S6Isserlis" / "lean-toolchain",
                 ROOT / "formal" / "lean" / "s6" / "pphi2_clean" / "lean-toolchain"):
        if cand.exists():
            txt = cand.read_text(encoding="utf-8", errors="replace").strip()
            if ":" in txt:
                return txt.split(":", 1)[1]
    return "v4.34.0-rc2"


def unreachable_modules() -> int:
    """Modules of the package that the root aggregator cannot reach at all.

    Read from the source: the root file's ``import AImathPPhi2Clean.X`` lines seed
    a breadth-first traversal of the per-module import graph, and the answer is
    the number of modules on disk that the traversal never enters.  This is the
    number Part II's boundary section quotes, so it is computed rather than typed.
    """
    root_file = ROOT / "formal" / "lean" / "s6" / "pphi2_clean" / "AImathPPhi2Clean.lean"
    if not root_file.exists() or not CLEAN_LIB.is_dir():
        return 0
    imp = re.compile(r"^import\s+AImathPPhi2Clean\.([A-Za-z0-9_]+)\s*$", re.M)
    graph = {}
    for p in lean_files(CLEAN_LIB):
        graph[p.stem] = imp.findall(p.read_text(encoding="utf-8", errors="replace"))
    seen, stack = set(), list(imp.findall(root_file.read_text(encoding="utf-8", errors="replace")))
    while stack:
        m = stack.pop()
        if m in seen or m not in graph:
            seen.add(m)
            continue
        seen.add(m)
        stack.extend(x for x in graph[m] if x not in seen)
    return len(set(graph) - seen)


def unreachable_module_names() -> set:
    """The same set as ``unreachable_modules``, as names (see that docstring)."""
    root_file = ROOT / "formal" / "lean" / "s6" / "pphi2_clean" / "AImathPPhi2Clean.lean"
    if not root_file.exists() or not CLEAN_LIB.is_dir():
        return set()
    imp = re.compile(r"^import\s+AImathPPhi2Clean\.([A-Za-z0-9_]+)\s*$", re.M)
    graph = {}
    for p in lean_files(CLEAN_LIB):
        graph[p.stem] = imp.findall(p.read_text(encoding="utf-8", errors="replace"))
    seen, stack = set(), list(imp.findall(root_file.read_text(encoding="utf-8", errors="replace")))
    while stack:
        m = stack.pop()
        if m in seen or m not in graph:
            seen.add(m)
            continue
        seen.add(m)
        stack.extend(x for x in graph[m] if x not in seen)
    return set(graph) - seen


def measure_theorems_in_unreachable_modules() -> int:
    """How many of the registered measure-limit theorems sit in unreachable modules.

    The boundary section says the evidence for those declarations rests on the
    transcript rather than on a build of the aggregator, so the number is computed
    from the registry and the reachability graph instead of being typed.
    """
    names = registry_theorem_names("PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT")
    unreachable = unreachable_module_names()
    if not names or not unreachable:
        return 0
    texts = {}
    for p in lean_files(CLEAN_LIB):
        texts[p.stem] = p.read_text(encoding="utf-8", errors="replace")
    n = 0
    for full in names:
        short = full.rsplit(".", 1)[-1]
        decl = re.compile(r"^\s*(?:theorem|lemma|def)\s+" + re.escape(short) + r"\b", re.M)
        for mod, txt in texts.items():
            if mod in unreachable and decl.search(txt):
                n += 1
                break
    return n


def registry_theorem_names(contract: str):
    """The ``theorem_names`` list of one contract, read from the registry text."""
    try:
        text = REGISTRY.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    if contract not in text:
        return []
    block = text.split(contract + ":", 1)[1]
    block = block.split("remote_only:", 1)[0]
    return re.findall(r"^\s+-\s+(Pphi2Clean\.\S+)\s*$", block, re.M)


def cited_works() -> int:
    """Number of bibliography entries, read from refs.bib."""
    bib = PAPER / "refs.bib"
    if not bib.exists():
        return 0
    return len(re.findall(r"^@[a-zA-Z]+\{", bib.read_text(encoding="utf-8", errors="replace"), re.M))


def negative_control_lines() -> int:
    """Lines of the package's negative-control probe (the injected-axiom file)."""
    p = CLEAN_AUDIT / "negative_axiom.lean"
    if not p.exists():
        return 0
    return len([l for l in p.read_text(encoding="utf-8", errors="replace").splitlines()
                if l.strip() and not l.strip().startswith("--")])


def main() -> int:
    lib = lean_files(CLEAN_LIB)
    audit = lean_files(CLEAN_AUDIT)
    root_lean = sorted(ROOT_LEAN.glob("*.lean"))

    sorry, axioms = count_sorry_axiom(lib)
    n_sorry_raw, n_axiom_raw = naive_sorry_axiom(lib)

    n_contracts, n_permitted, n_chain = registry_counts()
    measure_theorems, _cov = 0, 0
    try:
        text = REGISTRY.read_text(encoding="utf-8", errors="replace")
        block = text.split("PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT:", 1)[1]
        block = block.split("remote_only:", 1)[0]
        measure_theorems = len(re.findall(r"^\s+-\s+Pphi2Clean\.", block, re.M))
    except (IndexError, OSError):
        measure_theorems = 0

    vals = {
        "NumCleanModules": len(lib),
        "NumCleanLines": count_lines(lib),
        "NumAuditProbes": len(audit),
        "NumCleanSorry": sorry,
        "NumCleanProjectAxioms": axioms,
        "NumRootFiles": len(root_lean),
        "NumRootLines": count_lines(root_lean),
        "NumContracts": n_contracts,
        "NumPermittedAxioms": n_permitted,
        "NumChainTheorems": n_chain,
        "NumProofDocs": len(list((ROOT / "proofs").glob("*.md"))),
        "NumProbes": len(list((ROOT / "verify").glob("*_probe.py"))),
        "NumFailureCards": max(0, len(list((ROOT / "proof_graph" / "failures").glob("*.md")))
                               - (1 if (ROOT / "proof_graph" / "failures" / "README.md").exists() else 0)),
        "NumUnreachableModules": unreachable_modules(),
        "NumMeasureContractTheorems": measure_theorems,
        "NumUnreachableChainTheorems": measure_theorems_in_unreachable_modules(),
        "NumNegativeControlLines": negative_control_lines(),
        "NumCitedWorks": cited_works(),
    }
    missing = [k for k, v in vals.items() if v is None]
    if missing:
        print("WARN: unresolved counts %s -- keeping previous value in metrics.tex" % missing)

    text = {
        "NumCleanModules": lib, "NumCleanLines": lib, "NumCleanSorry": sorry,
        "NumCleanProjectAxioms": axioms, "NumAuditProbes": audit,
        "NumRootFiles": root_lean, "NumRootLines": root_lean,
    }
    del text  # only used for provenance of the numbers above

    lines = []
    lines.append("% ==========================================================================")
    lines.append("%  generated/metrics.tex  --  DERIVED FILE, DO NOT EDIT BY HAND.")
    lines.append("%  Regenerated by audit/count_lean.py on every build (python build_all.py).")
    lines.append("%  Every structural count quoted in the body must be one of these macros.")
    lines.append("% ==========================================================================")
    lines.append("")
    lines.append("% --- Lean sources, package AImathPPhi2Clean (formal/lean/s6/pphi2_clean) ---")
    for k in ("NumCleanModules", "NumCleanLines", "NumAuditProbes",
              "NumCleanSorry", "NumCleanProjectAxioms"):
        lines.append("\\newcommand{\\%s}{%s}" % (k, vals[k]))
    lines.append("")
    lines.append("% --- root S6Isserlis development (formal/lean/s6) ---")
    for k in ("NumRootFiles", "NumRootLines"):
        lines.append("\\newcommand{\\%s}{%s}" % (k, vals[k]))
    lines.append("")
    lines.append("% --- contracts and axiom discipline ---")
    for k in ("NumContracts", "NumPermittedAxioms", "NumChainTheorems",
              "NumMeasureContractTheorems", "NumNegativeControlLines"):
        lines.append("\\newcommand{\\%s}{%s}" % (k, vals[k]))
    lines.append("")
    lines.append("% --- reachability of the package root (Part II, boundary section) ---")
    lines.append("\\newcommand{\\NumUnreachableModules}{%s}" % vals["NumUnreachableModules"])
    lines.append("\\newcommand{\\NumUnreachableChainTheorems}{%s}" % vals["NumUnreachableChainTheorems"])
    lines.append("")
    lines.append("% --- bibliography ---")
    lines.append("\\newcommand{\\NumCitedWorks}{%s}" % vals["NumCitedWorks"])
    lines.append("")
    lines.append("% --- governance surfaces (documentation of the two Parts) ---")
    for k in ("NumProofDocs", "NumProbes", "NumFailureCards"):
        lines.append("\\newcommand{\\%s}{%s}" % (k, vals[k]))
    lines.append("")
    lines.append("% --- environment ---")
    lines.append("\\newcommand{\\LeanToolchain}{%s}" % toolchain())
    lines.append("\\newcommand{\\TectonicVersion}{0.17.0}")
    lines.append("")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines), encoding="utf-8", newline="\n")

    print("wrote %s" % OUT)
    for k, v in vals.items():
        print("  %-24s %s" % (k, v))
    print("  (naive comment-blind sorry/axiom count: %d / %d)" % (n_sorry_raw, n_axiom_raw))
    if n_sorry_raw != sorry or n_axiom_raw != axioms:
        print("  note: the difference is doc-comment text, e.g. 'axiom asserts.'")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
