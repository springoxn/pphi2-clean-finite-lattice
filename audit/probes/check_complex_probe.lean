import AImathPPhi2Clean.PeriodicHMinusTwoLatticeTrace
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Pphi2Clean.UpstreamLattice
def periodicComplexFourierProbe (L : ℝ) (hperiod : 0 < L)
    (k : Fin 2 → ℤ)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) : ℂ :=
  (ω (periodicCosineTest 2 L k hperiod) : ℂ) +
    (ω (periodicSineTest 2 L k hperiod) : ℂ) * Complex.I
@[simp] theorem periodicComplexFourierProbe_norm_sq (L : ℝ) (hperiod : 0 < L)
    (k : Fin 2 → ℤ)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) :
    ‖periodicComplexFourierProbe L hperiod k ω‖ ^ 2 =
      (ω (periodicCosineTest 2 L k hperiod)) ^ 2 +
        (ω (periodicSineTest 2 L k hperiod)) ^ 2 := by
  unfold periodicComplexFourierProbe
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]
end Pphi2Clean.Continuum
