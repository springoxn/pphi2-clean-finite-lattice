import AImathPPhi2Clean.PhysicalLatticeSampling
noncomputable section
namespace Pphi2Clean.Continuum
open scoped BigOperators

def probeCos (d : ℕ) (L : ℝ) (k : Fin d → ℤ) (hL : 0 < L) :
    BoundedContinuousFunction (Fin d → ℝ) ℝ :=
  ⟨⟨fun x => Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i), by fun_prop⟩,
    ⟨2, by
      intro x y
      rw [Real.dist_eq]
      calc
        |Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i) -
            Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| =
            |Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i) +
              -Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| := by rw [sub_eq_add_neg]
        _ ≤ |Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i)| +
              |-Real.cos ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)| := abs_add_le _ _
        _ ≤ 2 := by
          rw [abs_neg]
          linarith [Real.abs_cos_le_one ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * x i),
            Real.abs_cos_le_one ((2 * Real.pi / L) * ∑ i, (k i : ℝ) * y i)]⟩⟩
end Pphi2Clean.Continuum
