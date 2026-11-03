import Lake
open Lake DSL

package «AImathPPhi2Clean»

-- Without a `require`, the package can only be built from inside some *other*
-- project that happens to provide Mathlib, which is how it was built before
-- 2026-11-03 and why a reader could not build it from this directory at all.
-- The revision below is the one `lake-manifest.json` pins and the one the
-- recorded axiom transcript was produced against; the toolchain is fixed by
-- `lean-toolchain` (v4.34.0-rc2).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0-rc2"

lean_lib AImathPPhi2Clean
