import AImathPPhi2Clean.PhysicalLatticeSampling

noncomputable section
namespace Pphi2Clean.Continuum

open scoped BigOperators
open Pphi2Clean.UpstreamLattice

/-- Real cosine Fourier probe on the periodic physical torus, represented in
    the existing bounded-continuous test space. -/
def periodicCosineTest (d : ℕ) (L : ℝ) (k : Fin d → ℤ) (hL : 0 < L) :
    BoundedContinuousFunction (Fin d → ℝ) ℝ :=
  ⟨⟨fun x => Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i), by fun_prop⟩,
    ⟨2, by
      intro x y
      rw [Real.dist_eq]
      calc
        |Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i) -
            Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| =
            |Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i) +
              -Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| := by
                rw [sub_eq_add_neg]
        _ ≤ |Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i)| +
              |-Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| :=
          abs_add_le _ _
        _ ≤ 2 := by
          rw [abs_neg]
          linarith [Real.abs_cos_le_one
              ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i),
            Real.abs_cos_le_one
              ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)]⟩⟩

/-- Real sine Fourier probe on the periodic physical torus, represented in
    the existing bounded-continuous test space. -/
def periodicSineTest (d : ℕ) (L : ℝ) (k : Fin d → ℤ) (hL : 0 < L) :
    BoundedContinuousFunction (Fin d → ℝ) ℝ :=
  ⟨⟨fun x => Real.sin ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i), by fun_prop⟩,
    ⟨2, by
      intro x y
      rw [Real.dist_eq]
      calc
        |Real.sin ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i) -
            Real.sin ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| =
            |Real.sin ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i) +
              -Real.sin ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| := by
                rw [sub_eq_add_neg]
        _ ≤ |Real.sin ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i)| +
              |-Real.sin ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| :=
          abs_add_le _ _
        _ ≤ 2 := by
          rw [abs_neg]
          linarith [Real.abs_sin_le_one
              ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i),
            Real.abs_sin_le_one
              ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)]⟩⟩

@[simp] theorem periodicCosineTest_apply (d : ℕ) (L : ℝ) (k : Fin d → ℤ)
    (hL : 0 < L) (x : Fin d → ℝ) :
    periodicCosineTest d L k hL x =
      Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i) := rfl

@[simp] theorem periodicSineTest_apply (d : ℕ) (L : ℝ) (k : Fin d → ℤ)
    (hL : 0 < L) (x : Fin d → ℝ) :
    periodicSineTest d L k hL x =
      Real.sin ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i) := rfl

@[simp] theorem physicalTestEval_periodicCosineTest_apply (d N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (k : Fin d → ℤ) (hL : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites d N))) :
    physicalTestEval d N a j (periodicCosineTest d L k hL) =
      a ^ d * Real.cos ((2 * Real.pi / L) *
        ∑ i, (k i : ℝ) * latticePhysicalPoint d N a
          ((Fintype.equivFin (FinLatticeSites d N)).symm j) i) := rfl

@[simp] theorem physicalTestEval_periodicSineTest_apply (d N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (k : Fin d → ℤ) (hL : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites d N))) :
    physicalTestEval d N a j (periodicSineTest d L k hL) =
      a ^ d * Real.sin ((2 * Real.pi / L) *
        ∑ i, (k i : ℝ) * latticePhysicalPoint d N a
          ((Fintype.equivFin (FinLatticeSites d N)).symm j) i) := rfl

end Pphi2Clean.Continuum
