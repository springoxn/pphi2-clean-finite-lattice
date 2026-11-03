import Lake
open Lake DSL

package S6Isserlis

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Mark the library as the default target so that a bare 'lake build' builds everything.
-- Without it, 'lake build' reports "no default targets configured" and does nothing,
-- which is how a stale S2.olean survived unnoticed until 2026-09-18.
@[default_target]
lean_lib S6Isserlis
