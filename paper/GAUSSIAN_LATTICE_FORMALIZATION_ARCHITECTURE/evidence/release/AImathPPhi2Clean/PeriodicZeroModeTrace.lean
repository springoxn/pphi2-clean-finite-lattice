import AImathPPhi2Clean.PeriodicFullHMinusTwoTrace
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
@[simp] theorem periodicCosineTest_zero_eq_one (L : ℝ) (hperiod : 0 < L) :
    periodicCosineTest 2 L (0 : Fin 2 → ℤ) hperiod =
      (1 : BoundedContinuousFunction (Fin 2 → ℝ) ℝ) := by
  ext x
  simp [periodicCosineTest]
@[simp] theorem periodicSineTest_zero_eq_zero (L : ℝ) (hperiod : 0 < L) :
    periodicSineTest 2 L (0 : Fin 2 → ℤ) hperiod =
      (0 : BoundedContinuousFunction (Fin 2 → ℝ) ℝ) := by
  ext x
  simp [periodicSineTest]
theorem periodicComplexFourierLiftMoment_zero_le
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    periodicComplexFourierLiftMoment N a mass L ha hmass hperiod 0 ≤
      mass⁻¹ ^ 2 * L ^ 2 := by
  rw [periodicComplexFourierLiftMoment_eq N a mass L ha hmass hL hperiod 0]
  unfold periodicComplexFourierProbeMoment
  have h := physicalGJMeasure_fixed_volume_second_moment_le
    2 N a mass L ha hmass hL
    (1 : BoundedContinuousFunction (Fin 2 → ℝ) ℝ)
  calc
    (∫ ω, ‖periodicComplexFourierProbe L hperiod 0 ω‖ ^ 2 ∂
        physicalGJMeasure 2 N a mass ha hmass) =
      ∫ ω, (ω (1 : BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) ^ 2 ∂
        physicalGJMeasure 2 N a mass ha hmass := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [periodicComplexFourierProbe_norm_sq]
          rw [periodicCosineTest_zero_eq_one L hperiod,
            periodicSineTest_zero_eq_zero L hperiod]
          simp
    _ ≤ mass⁻¹ ^ 2 * L ^ 2 := by simpa using h
end Pphi2Clean.Continuum
