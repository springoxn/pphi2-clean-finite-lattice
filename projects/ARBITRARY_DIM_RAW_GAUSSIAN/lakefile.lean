import Lake
open Lake DSL

package «AImathPPhi2Clean»

-- Exact upstream revision used for the current periodic 2D/4D release.
-- Historical archive/extension transcripts are preserved separately.
-- lean-toolchain pins Lean v4.34.0-rc2; the lockfile pins inherited packages.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "852d20a84581aeba8527bd01d0be361d8c0e71c0"

lean_lib AImathPPhi2Clean
