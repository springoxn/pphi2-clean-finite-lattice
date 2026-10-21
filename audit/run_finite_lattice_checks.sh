#!/usr/bin/env bash
# Reproduce the finite-lattice migration and its dependency firewall.
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# Portable: override LAKE / LEAN / PYTHON in the environment if your
# toolchain lives elsewhere (elan's default location is assumed).
LAKE="${LAKE:-$HOME/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lake}"
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean}"
PYTHON="${PYTHON:-python3}"
UPSTREAM="${1:?usage: $0 <path to a GaussianField checkout at the pinned commit>}"
export LAKE LEAN PYTHON
cd "$ROOT"
"$LAKE" build AImathPPhi2Clean > audit/finite_lattice_build.log 2>&1
cat audit/finite_lattice_build.log
"$PYTHON" audit/check_upstream_finite_definitions.py --upstream "$UPSTREAM" > audit/upstream_finite_definitions.log 2>&1
cat audit/upstream_finite_definitions.log
bash audit/run_firewall.sh
printf '%s\n' 'ALL_FINITE_LATTICE_CHECKS_PASSED'
