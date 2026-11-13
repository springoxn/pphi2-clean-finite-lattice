#!/usr/bin/env bash
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# Portable: override LAKE / LEAN / PYTHON in the environment if your
# toolchain lives elsewhere (elan's default location is assumed).
LAKE="${LAKE:-$HOME/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lake}"
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean}"
PYTHON="${PYTHON:-python3}"
cd "$ROOT"
"$LAKE" env lean audit/clean_axioms.lean > audit/clean_axioms.log 2>&1
if grep -q "depends on axioms:.*injectedAxiom" audit/clean_axioms.log; then echo "FAIL: clean tree polluted"; exit 1; fi
"$LEAN" audit/negative_axiom.lean > audit/negative_axiom.log 2>&1
grep -q "injectedAxiom" audit/negative_axiom.log
echo "axiom firewall checks passed"
"$PYTHON" audit/run_interface_gate.py
