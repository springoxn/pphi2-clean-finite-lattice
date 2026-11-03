import AImathPPhi2Clean.RealFourierTestFunctions
noncomputable section
namespace Pphi2Clean.Continuum
open Pphi2Clean.UpstreamLattice
open scoped BigOperators
example (d N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (k : Fin d → ℤ)
    (hL : 0 < L) (j : Fin (Fintype.card (FinLatticeSites d N))) :
    physicalTestEval d N a j (periodicCosineTest d L k hL) =
      a ^ d * Real.cos ((2 * Real.pi / L) *
        ∑ i, (k i : ℝ) * latticePhysicalPoint d N a
          ((Fintype.equivFin (FinLatticeSites d N)).symm j) i) := by
  rfl
example (d N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (k : Fin d → ℤ)
    (hL : 0 < L) (j : Fin (Fintype.card (FinLatticeSites d N))) :
    physicalTestEval d N a j (periodicSineTest d L k hL) =
      a ^ d * Real.sin ((2 * Real.pi / L) *
        ∑ i, (k i : ℝ) * latticePhysicalPoint d N a
          ((Fintype.equivFin (FinLatticeSites d N)).symm j) i) := by
  rfl
end Pphi2Clean.Continuum
