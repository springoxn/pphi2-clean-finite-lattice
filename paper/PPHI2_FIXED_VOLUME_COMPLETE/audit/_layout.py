#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Where the Lean sources are, in this checkout.

The paper is one content of a repository that also hosts the development it
reports, and the two are laid out differently there than in the authors' working
tree: the published repository keeps the Lake package at its top level, because
the package came first, while the authors' tree keeps it under
`formal/lean/s6/pphi2_clean/`.  Hard-coding either path makes the scripts
unrunnable in the other tree -- so they ask here instead.

Resolution order, first hit wins:

    1. $PPHI2_LEAN_PACKAGE                     (explicit override)
    2. <repo>/formal/lean/s6/pphi2_clean       (authors' working tree)
    3. <repo>/lean/pphi2_clean
    4. <repo>                                  (published repository)

A candidate qualifies if it holds `AImathPPhi2Clean/` and `lakefile.lean`.  The
probe-file count is taken from the first of `audit/`, `audit/probes/` that holds
`.lean` files, so a checkout that publishes the probes under either name is
counted correctly.
"""
from __future__ import annotations

import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent
ROOT = PAPER.parent.parent


def package() -> Path:
    cands = [
        os.environ.get("PPHI2_LEAN_PACKAGE"),
        ROOT / "formal" / "lean" / "s6" / "pphi2_clean",
        ROOT / "lean" / "pphi2_clean",
        ROOT,
    ]
    for c in cands:
        if not c:
            continue
        p = Path(c)
        if (p / "AImathPPhi2Clean").is_dir() and (p / "lakefile.lean").is_file():
            return p
    raise SystemExit(
        "TOOL ERROR: no Lake package found; set $PPHI2_LEAN_PACKAGE. Tried: %s"
        % ", ".join(str(c) for c in cands if c))


def probe_dir(pkg: Path | None = None) -> Path:
    pkg = pkg or package()
    for name in ("audit/probes", "audit"):
        p = pkg / name if (pkg / name).is_dir() else None
        if p is None:
            continue
        if any(p.glob("*.lean")):
            return p
    return pkg / "audit"


def registry() -> Path:
    cands = [
        os.environ.get("PPHI2_REGISTRY"),
        ROOT / "formal" / "lean" / "challenges" / "_registry.yaml",
        package().parent / "challenges" / "_registry.yaml",
        ROOT / "challenges" / "_registry.yaml",
    ]
    for c in cands:
        if c and Path(c).is_file():
            return Path(c)
    raise SystemExit("TOOL ERROR: no _registry.yaml found; set $PPHI2_REGISTRY")


def root_development() -> Path:
    """The surrounding `s6` directory, if this checkout carries it."""
    return ROOT / "formal" / "lean" / "s6"
