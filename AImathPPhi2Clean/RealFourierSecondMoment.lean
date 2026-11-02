import AImathPPhi2Clean.RealFourierTestFunctions
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
open Pphi2Clean.UpstreamLattice
@[simp] theorem periodicCosineTest_norm_le_one (d : ℕ) (L : ℝ)
    (k : Fin d → ℤ) (hL : 0 < L) :
    ‖periodicCosineTest d L k hL‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num)]
  intro x
  rw [Real.norm_eq_abs]
  exact Real.abs_cos_le_one _
@[simp] theorem periodicSineTest_norm_le_one (d : ℕ) (L : ℝ)
    (k : Fin d → ℤ) (hL : 0 < L) :
    ‖periodicSineTest d L k hL‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num)]
  intro x
  rw [Real.norm_eq_abs]
  exact Real.abs_sin_le_one _
theorem physicalGJMeasure_periodicCosineTest_second_moment_le
    (d N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (k : Fin d → ℤ) (hperiod : 0 < L) :
    ∫ ω, (ω (periodicCosineTest d L k hperiod)) ^ 2 ∂
      physicalGJMeasure d N a mass ha hmass ≤ mass⁻¹ ^ 2 * L ^ d := by
  have h := physicalGJMeasure_fixed_volume_second_moment_le d N a mass L ha hmass hL
    (periodicCosineTest d L k hperiod)
  have hn := periodicCosineTest_norm_le_one d L k hperiod
  have hc : 0 ≤ mass⁻¹ ^ 2 * L ^ d := by positivity
  calc
    _ ≤ mass⁻¹ ^ 2 * L ^ d * ‖periodicCosineTest d L k hperiod‖ ^ 2 := h
    _ ≤ mass⁻¹ ^ 2 * L ^ d * 1 ^ 2 := by gcongr
    _ = mass⁻¹ ^ 2 * L ^ d := by ring
theorem physicalGJMeasure_periodicSineTest_second_moment_le
    (d N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (k : Fin d → ℤ) (hperiod : 0 < L) :
    ∫ ω, (ω (periodicSineTest d L k hperiod)) ^ 2 ∂
      physicalGJMeasure d N a mass ha hmass ≤ mass⁻¹ ^ 2 * L ^ d := by
  have h := physicalGJMeasure_fixed_volume_second_moment_le d N a mass L ha hmass hL
    (periodicSineTest d L k hperiod)
  have hn := periodicSineTest_norm_le_one d L k hperiod
  have hc : 0 ≤ mass⁻¹ ^ 2 * L ^ d := by positivity
  calc
    _ ≤ mass⁻¹ ^ 2 * L ^ d * ‖periodicSineTest d L k hperiod‖ ^ 2 := h
    _ ≤ mass⁻¹ ^ 2 * L ^ d * 1 ^ 2 := by gcongr
    _ = mass⁻¹ ^ 2 * L ^ d := by ring
end Pphi2Clean.Continuum
