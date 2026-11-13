import AImathPPhi2Clean.RealFourierTestFunctions
noncomputable section
namespace Pphi2Clean.Continuum
example (d : ℕ) (L : ℝ) (k : Fin d → ℤ) (hL : 0 < L) :
    ‖periodicCosineTest d L k hL‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num)]
  intro x
  rw [Real.norm_eq_abs]
  exact Real.abs_cos_le_one _
example (d : ℕ) (L : ℝ) (k : Fin d → ℤ) (hL : 0 < L) :
    ‖periodicSineTest d L k hL‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num)]
  intro x
  rw [Real.norm_eq_abs]
  exact Real.abs_sin_le_one _
end Pphi2Clean.Continuum
