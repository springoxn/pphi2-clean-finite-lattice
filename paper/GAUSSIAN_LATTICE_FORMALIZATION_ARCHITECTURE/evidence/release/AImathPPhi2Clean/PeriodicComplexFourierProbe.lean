import AImathPPhi2Clean.PeriodicHMinusTwoLatticeTrace
import AImathPPhi2Clean.PhysicalLatticeGaussianLaw
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
def periodicComplexFourierProbeMoment (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) (k : Fin 2 → ℤ) : ℝ :=
  ∫ ω, ‖periodicComplexFourierProbe L hperiod k ω‖ ^ 2 ∂
    physicalGJMeasure 2 N a mass ha hmass
theorem periodicComplexFourierProbeMoment_eq (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) (k : Fin 2 → ℤ) :
    periodicComplexFourierProbeMoment N a mass L ha hmass hperiod k =
      periodicFourierProbeMoment N a mass L ha hmass hL hperiod k := by
  unfold periodicComplexFourierProbeMoment periodicFourierProbeMoment
  have hcos := physicalGJMeasure_eval_hasGaussianLaw 2 N a mass ha hmass
    (periodicCosineTest 2 L k hperiod)
  have hsin := physicalGJMeasure_eval_hasGaussianLaw 2 N a mass ha hmass
    (periodicSineTest 2 L k hperiod)
  have hcosI : Integrable (fun ω =>
      (ω (periodicCosineTest 2 L k hperiod)) ^ 2)
      (physicalGJMeasure 2 N a mass ha hmass) := hcos.memLp_two.integrable_sq
  have hsinI : Integrable (fun ω =>
      (ω (periodicSineTest 2 L k hperiod)) ^ 2)
      (physicalGJMeasure 2 N a mass ha hmass) := hsin.memLp_two.integrable_sq
  rw [← integral_add hcosI hsinI]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact periodicComplexFourierProbe_norm_sq L hperiod k ω
theorem periodicHMinusTwo_complex_probe_trace_bound (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) :
    Summable (fun k => periodicHMinusTwoWeight k *
      periodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) ∧
      ∑' k, periodicHMinusTwoWeight k *
        periodicComplexFourierProbeMoment N a mass L ha hmass hperiod k ≤
        (2 * (mass⁻¹ ^ 2 * L ^ 2)) *
          ∑' k, periodicHMinusTwoWeight k := by
  have h := periodicHMinusTwo_lattice_probe_trace_bound N a mass L ha hmass hL hperiod
  rw [show (fun k => periodicHMinusTwoWeight k *
      periodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) =
      (fun k => periodicHMinusTwoWeight k *
        periodicFourierProbeMoment N a mass L ha hmass hL hperiod k) by
    funext k
    rw [periodicComplexFourierProbeMoment_eq N a mass L ha hmass hL hperiod k]]
  exact h
end Pphi2Clean.Continuum
