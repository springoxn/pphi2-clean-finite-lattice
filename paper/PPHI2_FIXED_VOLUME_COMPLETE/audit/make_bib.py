#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Render ``generated/bibliography.tex`` from ``refs.bib``.

Why not run BibTeX: the project builds with Tectonic from a **seeded offline
cache**, and that bundle contains no ``.bst`` files at all.  BibTeX therefore
fails with "I couldn't open style file amsplain.bst" -- and Tectonic *ignores*
that error, so the build stays green while every citation renders as [?].  That
is a silent failure of exactly the kind this repository's failure cards warn
about, so the bibliography is rendered here instead, deterministically, from the
single source of truth ``refs.bib``.

The output is an ordinary ``thebibliography`` environment, so amsart typesets it
with no external style file.  Sorting is alphabetical by citation key, which
makes the rendering independent of the order in which the body cites.

The parser is deliberately small but strict: brace-balanced values, one entry per
``@type{key, ...}``, and a hard error on anything it cannot classify.  It is not
a general BibTeX implementation and does not pretend to be.
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
BIB = PAPER / "refs.bib"
OUT = PAPER / "generated" / "bibliography.tex"


def parse_bib(text: str):
    """Return [(entry_type, key, {field: value})] with brace-balanced values."""
    entries = []
    for chunk in re.split(r"@", text)[1:]:
        m = re.match(r"\s*([A-Za-z]+)\s*\{\s*([^,\s]+)\s*,", chunk)
        if not m:
            continue
        etype, key = m.group(1).lower(), m.group(2)
        body = chunk[m.end():]
        fields = {}
        i = 0
        while i < len(body):
            fm = re.match(r"\s*([A-Za-z_]+)\s*=\s*\{", body[i:])
            if not fm:
                if body[i:].strip().startswith("}"):
                    break
                i += 1
                continue
            name = fm.group(1).lower()
            j = i + fm.end()
            depth, start = 1, j
            while j < len(body) and depth:
                if body[j] == "{":
                    depth += 1
                elif body[j] == "}":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            fields[name] = re.sub(r"\s+", " ", body[start:j]).strip()
            i = j + 1
        entries.append((etype, key, fields))
    return entries


def initials(author: str) -> str:
    """'Osterwalder, Konrad and Schrader, Robert' -> 'K. Osterwalder and R. Schrader'."""
    if author.startswith("{") and author.endswith("}"):
        return author[1:-1]
    people = [p.strip() for p in author.split(" and ")]
    out = []
    for p in people:
        if "," in p:
            last, first = [q.strip() for q in p.split(",", 1)]
            init = " ".join(f"{w[0]}." for w in first.replace(".", " ").split() if w)
            out.append(f"{init} {last}")
        else:
            out.append(p)
    if len(out) == 1:
        return out[0]
    return ", ".join(out[:-1]) + " and " + out[-1]


def render(etype: str, key: str, f: dict) -> str:
    au = initials(f.get("author", "")) if f.get("author") else ""
    title = f.get("title", "")
    head = f"{au}, " if au else ""
    if etype == "article":
        bits = [f"{head}\\emph{{{title}}}"]
        if f.get("journal"):
            j = f"\\emph{{{f['journal']}}}"
            if f.get("volume"):
                j += f" \\textbf{{{f['volume']}}}"
            if f.get("year"):
                j += f" ({f['year']})"
            if f.get("pages"):
                j += f", {f['pages']}"
            bits.append(j)
        elif f.get("year"):
            bits.append(f["year"])
    elif etype == "book":
        bits = [f"{head}\\emph{{{title}}}"]
        tail = []
        if f.get("series"):
            s = f["series"]
            if f.get("volume"):
                s += f" {f['volume']}"
            tail.append(s)
        if f.get("edition"):
            tail.append(f"{f['edition']} ed.")
        if f.get("publisher"):
            tail.append(f["publisher"])
        if f.get("year"):
            tail.append(f["year"])
        if tail:
            bits.append(", ".join(tail))
    elif etype in ("misc", "online"):
        bits = [f"{head}\\emph{{{title}}}"]
        if f.get("note"):
            bits.append(f["note"])
        if f.get("year"):
            bits.append(f["year"])
    else:
        raise SystemExit("PREFLIGHT FAIL: unhandled entry type %r for key %r" % (etype, key))
    return "\\bibitem{%s}\n%s." % (key, ", ".join(x for x in bits if x))


def main() -> int:
    if not BIB.exists():
        raise SystemExit("PREFLIGHT FAIL: %s missing" % BIB)
    entries = parse_bib(BIB.read_text(encoding="utf-8", errors="replace"))
    if not entries:
        raise SystemExit("PREFLIGHT FAIL: no entries parsed from %s" % BIB)
    keys = [k for _, k, _ in entries]
    if len(set(keys)) != len(keys):
        raise SystemExit("PREFLIGHT FAIL: duplicate citation keys in refs.bib")
    L = []
    L.append("% ===== generated/bibliography.tex -- DERIVED, DO NOT EDIT =====")
    L.append("% Rendered by audit/make_bib.py from refs.bib.")
    L.append("% A thebibliography environment is used because the offline Tectonic")
    L.append("% bundle contains no .bst files; BibTeX would fail silently.")
    L.append("")
    L.append("\\begin{thebibliography}{%d}" % max(9, len(entries)))
    L.append("")
    for etype, key, f in sorted(entries, key=lambda e: e[1]):
        L.append(render(etype, key, f))
        L.append("")
    L.append("\\end{thebibliography}")
    L.append("")
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(L), encoding="utf-8", newline="\n")
    print("wrote %s (%d entries, alphabetical by key)" % (OUT, len(entries)))
    print("keys: " + ", ".join(sorted(keys)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
