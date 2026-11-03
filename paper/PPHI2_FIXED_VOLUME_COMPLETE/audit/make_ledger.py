#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Regenerate ``generated/ledger.tex`` and ``generated/axioms.tex``.

Two derived appendices:

  ledger.tex  the declaration ledger -- for every theorem this paper reports,
              its fully qualified Lean name, its module, and its role in the
              argument.  Built from two single providers:
                * the statement registry  formal/lean/challenges/_registry.yaml
                  (names and modules; the machine-readable source of the
                  node -> declaration link)
                * a curated role table below (prose, one line per declaration)
              A name in the registry with no role, or a role with no registry
              entry, is a hard error: the ledger may not silently drift.

  axioms.tex  the axiom-footprint transcript -- rendered from
              ext/axiom_transcript.txt, which records the verbatim engine
              output.  Every footprint must lie inside the permitted set
              declared by the registry; a footprint outside it is a hard
              error.

Why generated rather than typed: the paper's central claim is a claim about
Lean declarations.  Typing those names by hand would let a typo survive review.
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
ROOT = PAPER.parent.parent
REGISTRY = ROOT / "formal" / "lean" / "challenges" / "_registry.yaml"
TRANSCRIPT = PAPER / "ext" / "axiom_transcript.txt"

# (node, [(declaration, module, role)])
# The role strings are prose and are the only hand-maintained content here.
ROLES = {
    "PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT": [
        ("Pphi2Clean.Continuum.fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing",
         "PeriodicFourierCovarianceLimit",
         "fixed-volume convergence of the lattice covariance pairing to the torus Green pairing"),
        ("Pphi2Clean.Continuum.physicalGJMeasure_fixedVolume_mixedMoment_tendsto_torusFourierGreenPairing",
         "PeriodicFourierCovarianceLimit",
         "the same limit for the mixed second moment of the physical lattice law"),
        ("Pphi2Clean.Continuum.physicalGJMeasure_fixedVolume_covariance_tendsto_torusFourierGreenPairing",
         "PeriodicFourierCovarianceLimit",
         "the same limit for the centred covariance; this is the input the weak-limit theorem consumes"),
    ],
    "PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT": [
        ("Pphi2Clean.Continuum.periodicHMinusThreeCompletion_separable",
         "PeriodicHMinusThreeTopologyBorel",
         "the carrier is separable, and complete by the completion; separable and complete gives Polish, which is what carries the Prokhorov machinery"),
        ("Pphi2Clean.Continuum.periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals",
         "PeriodicHMinusThreeWeakLimitMarginal",
         "two Borel probability measures agreeing on every indexed cylinder agree"),
        ("Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_subsequential_limit_has_expected_cylinder",
         "PeriodicHMinusThreeWeakLimitMarginal",
         "the finite-mode limits pass to any subsequential limit extracted by Prokhorov"),
        ("Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_exists",
         "PeriodicHMinusThreeWeakLimitMarginal",
         "existence of a weak limit point of the whole sequence"),
        ("Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_has_expected_cylinder",
         "PeriodicHMinusThreeWeakLimitMarginal",
         "that limit point has the prescribed finite Fourier marginals"),
        ("Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_unique",
         "PeriodicHMinusThreeWeakLimitMarginal",
         "any two limit points coincide, so the limit is independent of the subsequence"),
        ("Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders",
         "PeriodicHMinusThreeWeakLimitMarginal",
         "the main theorem: whole-sequence weak convergence to the uniquely determined law"),
    ],
}


def registry_challenges() -> dict:
    """Return {challenge: {'modules': [...], 'theorem_names': [...]}}."""
    text = REGISTRY.read_text(encoding="utf-8", errors="replace")
    body = text.split("\nchallenges:", 1)
    out: dict = {}
    if len(body) != 2:
        return out
    cur = None
    field = None
    for line in body[1].splitlines():
        if re.match(r"^(imported_nodes|unwired):", line):
            break
        m = re.match(r"^  ([A-Z0-9_]+):\s*$", line)
        if m:
            cur = m.group(1)
            out[cur] = {"modules": [], "theorem_names": []}
            field = None
            continue
        k = re.match(r"^    ([a-z_]+):", line)
        if k and cur:
            field = k.group(1)
            continue
        if cur and field in ("modules", "theorem_names") and re.match(r"^\s+-\s+\S", line):
            out[cur][field].append(line.strip()[2:].strip())
    return out


def permitted() -> set:
    text = REGISTRY.read_text(encoding="utf-8", errors="replace")
    m = re.search(r"^permitted_axioms:\s*\[(.*?)\]", text, re.M)
    return {x.strip() for x in m.group(1).split(",") if x.strip()} if m else set()


def read_transcript():
    rows = []
    for line in TRANSCRIPT.read_text(encoding="utf-8", errors="replace").splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if "\t" not in s:
            raise SystemExit("PREFLIGHT FAIL: transcript line without TAB: %r" % s[:60])
        name, foot = s.split("\t", 1)
        rows.append((name.strip(), [x.strip() for x in foot.split(",") if x.strip()]))
    return rows


def draw_name(name: str) -> str:
    """Typeset a Lean identifier so that it can break at its underscores.

    A Lean identifier is longer than any table column, and an unbreakable run of
    monospaced text runs into the next column silently (an earlier version did
    exactly that).  The name is therefore emitted as one ``\\detokenize`` chunk
    per underscore-separated segment, joined by a breakable underscore: the
    rendered glyphs are identical, and TeX has somewhere to break.  The chunk
    form is also what ``audit/verify_paper.py`` reads the names back from.
    """
    chunks = name.split("_")
    return "\\texttt{%s}" % "\\_\\allowbreak{}".join("\\detokenize{%s}" % c for c in chunks)


def draw_footprint(items) -> str:
    """Typeset the axiom footprint with a break opportunity after each comma."""
    return "\\texttt{%s}" % ",\\allowbreak{} ".join(items)


def build_ledger_tex(challenges: dict) -> str:
    L = []
    L.append("% ===== generated/ledger.tex -- DERIVED, DO NOT EDIT =====================")
    L.append("% Built by audit/make_ledger.py from formal/lean/challenges/_registry.yaml")
    L.append("% and the role table in that script.  Every name here is a name the")
    L.append("% audit transcript reports a footprint for.")
    L.append("")
    L.append("Every declaration frozen in the two statement contracts is listed")
    L.append("below with its fully")
    L.append("qualified Lean~4 name, the module of the delivered package that declares")
    L.append("it, and its role in the argument.  The names are reproduced mechanically")
    L.append("from the statement registry of the development, so that the reader can")
    L.append("locate each claim in the sources without transcribing an underscore.")
    L.append("Declarations that the body quotes but that are not frozen in a contract")
    L.append("are named in the correspondence table of the Lean overview section,")
    L.append("which is where their role is described; this appendix does not claim to")
    L.append("list them, and the paper's gate checks them against the Lean sources.")
    L.append("")
    for node, roles in ROLES.items():
        regd = set(challenges.get(node, {}).get("theorem_names", []))
        mine = {r[0] for r in roles}
        if regd != mine:
            raise SystemExit(
                "PREFLIGHT FAIL: role table and registry disagree for %s\n"
                "  only in registry: %s\n  only in roles:    %s"
                % (node, sorted(regd - mine), sorted(mine - regd)))
        # A starred subsection in amsart is typeset run-in with a trailing period,
        # which looks like a typo in a heading whose text is an uppercase key.
        # A bold standalone line says the same thing without the punctuation.
        L.append("\\medskip\\noindent\\textbf{%s}\\par\\smallskip"
                 % node.replace("_", "\\_"))
        L.append("")
        L.append("\\begin{center}")
        L.append("\\footnotesize")
        L.append("\\begin{tabular}{@{}p{0.47\\linewidth}p{0.49\\linewidth}@{}}")
        L.append("\\toprule")
        L.append("Declaration & Module, and its role in the argument \\\\")
        L.append("\\midrule")
        for name, module, role in roles:
            short = name.split(".", 2)[-1]
            # The module goes on its own line inside the wide second column: a
            # CamelCase module name is a single unbreakable word, so it needs a
            # column wide enough for the longest of them, while the role prose
            # beside it would otherwise squeeze the declaration column.
            # audit/verify_paper.py reads declarations from the first cell only.
            L.append("%s & \\texttt{%s}\\newline %s \\\\" % (draw_name(short), module, role))
        L.append("\\bottomrule")
        L.append("\\end{tabular}")
        L.append("\\end{center}")
        L.append("")
    L.append("The prefix \\texttt{Pphi2Clean.Continuum} is common to all ten names")
    L.append("and is omitted in the table.")
    L.append("")
    return "\n".join(L)


def build_axioms_tex(rows, permitted_set) -> str:
    bad = [(n, f) for n, f in rows if not set(f) <= permitted_set]
    if bad:
        raise SystemExit("PREFLIGHT FAIL: footprint outside permitted set: %s" % bad)
    if len({tuple(f) for _, f in rows}) != 1:
        raise SystemExit("PREFLIGHT FAIL: noted footprints are not all equal; report them individually")
    L = []
    L.append("% ===== generated/axioms.tex -- DERIVED, DO NOT EDIT =====================")
    L.append("% Built by audit/make_ledger.py from ext/axiom_transcript.txt.")
    L.append("")
    L.append("The transcript below was produced by \\texttt{\\#print axioms} inside the")
    L.append("delivered Lake project, after the library target was built: the command")
    L.append("\\texttt{lake build AImathPPhi2Clean} elaborates every module of the")
    L.append("package, including the ones the root aggregator does not reach.  The")
    L.append("commands and the engine output are in")
    L.append("\\texttt{ext/axiom\\_transcript.txt} of the source tree; nothing here is")
    L.append("paraphrased.")
    L.append("")
    L.append("\\begin{center}")
    L.append("\\footnotesize")
    L.append("\\begin{tabular}{@{}p{0.60\\linewidth}p{0.34\\linewidth}@{}}")
    L.append("\\toprule")
    L.append("Declaration (prefix \\texttt{Pphi2Clean.Continuum} omitted) & Axiom footprint \\\\")
    L.append("\\midrule")
    for name, foot in rows:
        L.append("%s & %s \\\\" %
                 (draw_name(name.split(".", 2)[-1]), draw_footprint(foot)))
    L.append("\\bottomrule")
    L.append("\\end{tabular}")
    L.append("\\end{center}")
    L.append("")
    permitted_tex = ", ".join("\\texttt{%s}" % x for x in sorted(permitted_set))
    L.append("The permitted set of the development is %s, i.e.\\ exactly the three"
             % permitted_tex)
    L.append("axioms of the Lean kernel and \\texttt{Mathlib}.  In particular no")
    L.append("declaration above depends on an axiom introduced by the project, and none")
    L.append("depends on \\texttt{sorryAx}.")
    L.append("")
    return "\n".join(L)


def main() -> int:
    if not REGISTRY.exists():
        raise SystemExit("PREFLIGHT FAIL: registry not found at %s" % REGISTRY)
    if not TRANSCRIPT.exists():
        raise SystemExit("PREFLIGHT FAIL: transcript not found at %s" % TRANSCRIPT)
    challenges = registry_challenges()
    rows = read_transcript()
    pset = permitted()

    names_in_ledger = {n for roles in ROLES.values() for n, _, _ in roles}
    names_in_transcript = {n for n, _ in rows}
    if names_in_ledger != names_in_transcript:
        raise SystemExit(
            "PREFLIGHT FAIL: ledger and transcript disagree\n"
            "  only in ledger:     %s\n  only in transcript: %s"
            % (sorted(names_in_ledger - names_in_transcript),
               sorted(names_in_transcript - names_in_ledger)))

    (PAPER / "generated").mkdir(parents=True, exist_ok=True)
    (PAPER / "generated" / "ledger.tex").write_text(build_ledger_tex(challenges),
                                                   encoding="utf-8", newline="\n")
    (PAPER / "generated" / "axioms.tex").write_text(build_axioms_tex(rows, pset),
                                                   encoding="utf-8", newline="\n")
    print("wrote generated/ledger.tex (%d declarations) and generated/axioms.tex (%d rows)"
          % (len(names_in_ledger), len(rows)))
    print("permitted axioms: %s" % sorted(pset))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
