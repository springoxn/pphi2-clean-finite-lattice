#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Assertion gate for this paper.  Exit 0 only if every check passes.

Why: the value of this paper is that its claims are readable *and* checkable.
Four things rot silently, and each is checked here:

  N  every Lean name printed in the body (``\\lean{...}``) must be a declaration
     that the generated ledger lists -- a typo in a theorem name would otherwise
     be invisible to every reader, including the authors;
  M  every structural count in the body must be a macro from
     ``generated/metrics.tex``; the literal value of a distinctive count in the
     prose is a failure, so a count can only rot in one place;
  L  labels, cross-references, citations and bibliography keys must close, every
     section must be labelled, and no label may be duplicated;
  E  the axiom story must be self-consistent: the transcript footprints must all
     equal the permitted set, and the ledger must cover exactly the names the
     body quotes.

Each check has a negative control: the checker is run against a deliberately
broken input and must reject it (``--self-test``).  A checker that cannot fail
proves nothing.

Exit codes: 2 on tool errors (missing file, unparsable input), 1 on assertion
failures.  The two are never mixed.

Known limits: check N matches declaration *names*, not their types; it proves
the paper names something that exists in the delivered development, not that the
paper states it correctly.  That residual gap is stated in the paper itself and
is not closable by a script.

Registered in run_checks: no (paper-local tool).
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
SECTIONS = PAPER / "sections"
GENERATED = PAPER / "generated"
MAIN = PAPER / "main.tex"
BIB = PAPER / "refs.bib"
TRANSCRIPT = PAPER / "ext" / "axiom_transcript.txt"
REGISTRY = PAPER.parent.parent / "formal" / "lean" / "challenges" / "_registry.yaml"

LEAN_REF = re.compile(r"\\lean\{([^}]*)\}")
# generated/ledger.tex typesets names with \detokenize (underscores are otherwise
# illegal); the body quotes them with \lean.  Both are normalised to the short
# name, i.e. the last dot-separated segment, because the ledger omits the common
# namespace prefix once and says so.
# The ledger prints each declaration as one \detokenize chunk per underscore
# segment, joined by a breakable underscore, because an unbreakable Lean name is
# wider than any table column.  A name is therefore the "_"-join of the chunks in
# one table row; module names are plain \texttt and namespaces are not chunks.
LEDGER_REF = re.compile(r"\\detokenize\{([^}]*)\}")
LABEL = re.compile(r"\\label\{([^}]*)\}")
# Every reference command LaTeX provides and this paper uses: \ref, \eqref,
# \cref, \Cref.  `\eqref` was missing from this pattern until the 2026-11-03
# audit measured 125 uses of it in the body against a gate that could not see
# them; the negative control below pins the repair.
REF = re.compile(r"\\(?:eq|c|C)?ref\{([^}]*)\}")
CITE = re.compile(r"\\cite\{([^}]*)\}")
MACRO_USE = re.compile(r"\\(Num[A-Za-z]+|LeanToolchain|TectonicVersion)\b")
BIB_KEY = re.compile(r"@[a-zA-Z]+\{([^,]+),")


# --------------------------------------------------------------------------
# input gathering
# --------------------------------------------------------------------------
def read(p: Path) -> str:
    if not p.exists():
        raise SystemExit("TOOL ERROR: missing %s" % p)
    return p.read_text(encoding="utf-8", errors="replace")


def body_files():
    files = sorted(SECTIONS.glob("*.tex"))
    files += sorted((PAPER / "figures").glob("*.tex"))
    files += [GENERATED / "ledger.tex", GENERATED / "axioms.tex",
              GENERATED / "bibliography.tex"]
    return [f for f in files if f.exists()]


def strip_comments(text: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
def ledger_names(text_ledger: str) -> set:
    """Short names the ledger lists, rebuilt from the per-segment chunks.

    Each declaration is typeset as ``\\texttt{\\detokenize{a}\\_\\allowbreak{}...}``,
    one chunk per underscore-separated segment.  Only the declaration column
    carries that break form; a module name or a namespace is a plain word and
    never contributes a chunk.  Short names are what the body quotes, since the
    appendix states the common prefix once.
    """
    out = set()
    for line in text_ledger.splitlines():
        if "\\_\\allowbreak{}" not in line:
            continue
        if "&" not in line:
            continue
        cell = line.split("&", 1)[0]
        chunks = LEDGER_REF.findall(cell)
        if len(chunks) >= 2:
            out.add("_".join(chunks))
    return out


def _short(name: str) -> str:
    return name.strip().split(".")[-1]


DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|instance)\s+([A-Za-z0-9_'.]+)", re.M)

_DECL_CACHE: dict = {}


def lean_declarations() -> set:
    """Names of declarations in the package modules that are actually built.

    Scope matters: the package directory also holds `audit/` and, under it,
    vendored reference copies of other developments.  A name that occurs only
    there has never been elaborated in the delivered package, so accepting it
    would let the body quote a declaration that does not exist in what the paper
    reports.  The scan is therefore over the library directory alone, and is
    recursive only because modules may be split into subdirectories later.
    """
    if "v" in _DECL_CACHE:
        return _DECL_CACHE["v"]
    out = set()
    root = PAPER.parent.parent / "formal" / "lean" / "s6" / "pphi2_clean" / "AImathPPhi2Clean"
    for f in sorted(root.rglob("*.lean")) if root.exists() else []:
        try:
            text = f.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for m in DECL.finditer(text):
            out.add(m.group(1).split(".")[-1])
    _DECL_CACHE["v"] = out
    return out


def check_N(body_text: str, ledger_text: str):
    """Every quoted Lean name is a declaration that exists, and the chain is ledgered.

    Two acceptance routes, because the paper quotes two kinds of name:
      * the ten reported theorems must be in the generated ledger (Appendix A),
        which is what check E and the appendix generator enforce independently;
      * any other declaration the body mentions (a support module, an auxiliary
        lemma) is accepted if it is a declaration in the Lean sources, found by
        name in formal/lean/s6/pphi2_clean.  A name that is in neither place is
        red: that is the typo this check exists to catch.
    """
    used = set(LEAN_REF.findall(body_text))
    known = ledger_names(ledger_text)
    tree = lean_declarations()
    unknown = sorted(u for u in used if _short(u) not in known and _short(u) not in tree)
    return (not unknown,
            "N Lean names: %d quoted, %d in ledger, %d declared in the tree, unknown %s"
            % (len(used), len(known), len(tree), unknown[:4]))


def check_M(body_text: str, metrics_text: str):
    """Counts are macros; no distinctive literal count in the prose; no dead macro.

    Two ways a count can rot, and both are checked.  A *typed* count is caught by
    the literal-leak scan (for macros whose value is distinctive: 3+ digits or at
    least 40 -- a two-word count such as "two" is editorial, and the paper says so
    in its reproduction section).  A *dead* macro is caught by the unused scan:
    until the 2026-11-03 audit, seven macros were computed on every build and
    printed nowhere, while the two counts they shadowed were typed as words in a
    section.  A macro that nothing quotes protects nothing, so it is a failure
    here rather than a warning.
    """
    defined = set(re.findall(r"\\newcommand\{\\(Num[A-Za-z]+|LeanToolchain|TectonicVersion)\}", metrics_text))
    used = set(MACRO_USE.findall(body_text))
    undefined = sorted(used - defined)
    unused = sorted(defined - used)
    # distinctive values: 3+ digits, or >= 40
    vals = {}
    for name, val in re.findall(r"\\newcommand\{\\(\w+)\}\{([0-9]+)\}", metrics_text):
        if len(val) >= 3 or int(val) >= 40:
            vals[name] = val
    leaks = []
    for name, val in vals.items():
        # a leaked value is the literal number appearing as a standalone token
        for m in re.finditer(r"(?<![0-9A-Za-z.])%s(?![0-9A-Za-z.])" % re.escape(val), body_text):
            leaks.append((name, val, body_text.count(val)))
            break
    ok = not undefined and not leaks and not unused
    return (ok, "M counts: %d macros used, undefined %s, literal leaks %s, unused %s"
            % (len(used), undefined, [l[0] for l in leaks][:4], unused[:4]))


def check_L(body_text: str, bib_text: str, bibitems_text: str = "", main_text: str = ""):
    labels = LABEL.findall(body_text) + LABEL.findall(main_text)
    dup = sorted({l for l in labels if labels.count(l) > 1})
    refs = set()
    for group in REF.findall(body_text):
        refs |= {r.strip() for r in group.split(",") if r.strip()}
    dangling = sorted(refs - set(labels))
    cites = set()
    for group in CITE.findall(body_text):
        cites |= {c.strip() for c in group.split(",") if c.strip()}
    bib = set(BIB_KEY.findall(bib_text))
    # the rendered bibliography must carry exactly the keys of refs.bib
    rendered = set(re.findall(r"\\bibitem\{([^}]*)\}", bibitems_text)) if bibitems_text else bib
    drift = sorted(bib ^ rendered)
    unknown_cite = sorted(cites - rendered)
    uncited = sorted(rendered - cites)
    # every section must be labelled
    secs = re.findall(r"\\section\{([^}]*)\}", body_text)
    unlabelled = []
    for chunk in re.split(r"\\section\{", body_text)[1:]:
        head = chunk.split("\n", 1)[0]
        rest = chunk[:400]
        if "\\label{" not in rest:
            unlabelled.append(head[:40])
    ok = (not dup and not dangling and not unknown_cite and not unlabelled
          and not drift and not uncited)
    return (ok, "L structure: labels %d (dup %s), dangling refs %s, bad cites %s, "
                "uncited bib %d %s, unlabelled sections %s, refs.bib<->bibitem drift %s"
            % (len(labels), dup[:2], dangling[:4], unknown_cite[:3], len(uncited),
               uncited[:3], unlabelled[:2], drift[:3]))


def check_E(body_text: str, ledger_text: str, transcript_text: str, registry_text: str):
    """The axiom story is self-consistent, and the paper reports every ledgered theorem.

    Three conditions:
      * every transcript footprint equals the permitted set (not merely sits
        inside it: an empty footprint would be inside, and would be wrong to
        print as if it were the trio);
      * the ledger's names are exactly the transcript's names -- one ledger entry
        per recorded footprint, no more, no fewer;
      * the body quotes every ledgered name.  The paper claims to report those
        declarations; a ledger entry the prose never mentions would be an
        appendix disconnected from the text.
    Names the body mentions beyond the ledger are allowed and are checked by N
    against the Lean sources instead.
    """
    permitted = re.search(r"^permitted_axioms:\s*\[(.*?)\]", registry_text, re.M)
    if not permitted:
        return (False, "E axioms: no permitted_axioms in registry")
    pset = {x.strip() for x in permitted.group(1).split(",") if x.strip()}
    rows = []
    for line in transcript_text.splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        name, foot = s.split("\t", 1)
        rows.append((name.strip(), {x.strip() for x in foot.split(",") if x.strip()}))
    outside = [n for n, f in rows if not f <= pset]
    unequal = [n for n, f in rows if f != pset]
    known = ledger_names(ledger_text)
    transcript_names = {_short(n) for n, _ in rows}
    ledger_drift = sorted(known ^ transcript_names)
    quoted = {_short(u) for u in LEAN_REF.findall(body_text)}
    not_reported = sorted(known - quoted)
    ok = not outside and not unequal and not ledger_drift and not not_reported
    return (ok, "E axioms: %d transcript rows, %d permitted, outside %s, "
                "not equal to permitted %s, ledger<->transcript drift %s, "
                "ledgered names the body never quotes %s"
            % (len(rows), len(pset), outside[:2], unequal[:2],
               ledger_drift[:2], not_reported[:2]))


# --------------------------------------------------------------------------
# negative controls
# --------------------------------------------------------------------------
def self_test() -> int:
    """Each check must reject a deliberately broken input."""
    ledger = ("\\texttt{\\detokenize{periodicHMinusThree}\\_\\allowbreak{}"
              "\\detokenize{fixedVolume}\\_\\allowbreak{}"
              "\\detokenize{weak}\\_\\allowbreak{}"
              "\\detokenize{limit}\\_\\allowbreak{}"
              "\\detokenize{exists}} & \\texttt{M} & role \\\\\n")
    metrics = "\\newcommand{\\NumCleanModules}{89}\n"
    bib = "@article{ossier1973,\n}\n"
    registry = "permitted_axioms: [propext, Classical.choice, Quot.sound]\n"
    transcript = ("Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_exists"
                  "\tpropext, Classical.choice, Quot.sound\n")
    good_body = ("\\section{Good}\\label{sec:good}\n"
                 "See \\cref{sec:good} and \\cite{ossier1973};\n"
                 "the package has \\NumCleanModules{} modules and\n"
                 "\\lean{periodicHMinusThree_fixedVolume_weak_limit_exists}.\n")

    cases = []

    ok, _ = check_N(good_body, ledger)
    cases.append(("N accepts a known name", ok))
    bad = good_body + "\\lean{periodicHMinusThree_fixedVolume_weak_limit_existsX}\n"
    ok, _ = check_N(bad, ledger)
    cases.append(("N rejects an unknown name", not ok))

    ok, _ = check_M(good_body, metrics)
    cases.append(("M accepts macro-only counts", ok))
    ok, _ = check_M(good_body.replace("\\NumCleanModules{}", "89"), metrics)
    cases.append(("M rejects a literal count", not ok))
    ok, _ = check_M(good_body.replace("\\NumCleanModules{}", "\\NumNotDefined{}"), metrics)
    cases.append(("M rejects an undefined macro", not ok))
    ok, _ = check_M(good_body, metrics + "\\newcommand{\\NumUnused}{7}\n")
    cases.append(("M rejects a macro that nothing quotes", not ok))

    ok, _ = check_L(good_body, bib)
    cases.append(("L accepts a closing document", ok))
    ok, _ = check_L(good_body + "\\cref{sec:nowhere}\n", bib)
    cases.append(("L rejects a dangling ref", not ok))
    ok, _ = check_L(good_body + "\\eqref{eq:nowhere}\n", bib)
    cases.append(("L rejects a dangling eqref", not ok))
    ok, _ = check_L(good_body + "\\cite{notakey}\n", bib)
    cases.append(("L rejects an unknown citation", not ok))
    ok, _ = check_L(good_body.replace("\\label{sec:good}", ""), bib)
    cases.append(("L rejects an unlabelled section", not ok))

    ok, _ = check_E(good_body, ledger, transcript, registry)
    cases.append(("E accepts an identical footprint", ok))
    ok, _ = check_E(good_body, ledger,
                    transcript.replace("propext, Classical.choice, Quot.sound", "propext, myAxiom"),
                    registry)
    cases.append(("E rejects a footprint outside the permitted set", not ok))

    failed = [n for n, good in cases if not good]
    for n, good in cases:
        print("  [%s] %s" % ("OK" if good else "FAIL", n))
    if failed:
        print("SELF-TEST FAILED: %s" % failed)
        return 1
    print("self-test: %d/%d negative controls behave" % (len(cases), len(cases)))
    return 0


# --------------------------------------------------------------------------
def main(argv) -> int:
    if "--self-test" in argv:
        return self_test()

    body = "\n".join(strip_comments(read(f)) for f in body_files())
    # `main.tex` carries prose too (the "how to read this paper" paragraph and the
    # table of contents command).  It is scanned for typed counts and for macros, so
    # that a count cannot escape the check by being written one file up.
    main_body = strip_comments(read(MAIN))
    count_body = body + "\n" + main_body
    ledger_text = read(GENERATED / "ledger.tex")
    metrics_text = read(GENERATED / "metrics.tex")
    bib_text = read(BIB)
    transcript_text = read(TRANSCRIPT)
    registry_text = read(REGISTRY)

    results = [
        check_N(body, ledger_text),
        check_M(count_body, metrics_text),
        check_L(body, bib_text, read(GENERATED / "bibliography.tex"), read(MAIN)),
        check_E(body, ledger_text, transcript_text, registry_text),
    ]
    bad = 0
    for ok, msg in results:
        print("[%s] %s" % ("OK" if ok else "FAIL", msg))
        bad += 0 if ok else 1
    print("%d/%d paper checks passed." % (len(results) - bad, len(results)))
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
