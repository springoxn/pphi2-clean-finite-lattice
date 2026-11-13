import AImathPPhi2Clean.PeriodicHMinusTwoTraceMajorant
import AImathPPhi2Clean.RealFourierSecondMoment
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Pphi2Clean.UpstreamLattice
def periodicFourierProbeMoment (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L)
    (k : Fin 2 → ℤ) : ℝ :=
  (∫ ω, (ω (periodicCosineTest 2 L k hperiod)) ^ 2 ∂
      physicalGJMeasure 2 N a mass ha hmass) +
    (∫ ω, (ω (periodicSineTest 2 L k hperiod)) ^ 2 ∂
      physicalGJMeasure 2 N a mass ha hmass)
theorem periodicFourierProbeMoment_nonneg (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) (k : Fin 2 → ℤ) :
    0 ≤ periodicFourierProbeMoment N a mass L ha hmass hL hperiod k := by
  unfold periodicFourierProbeMoment
  positivity
theorem periodicFourierProbeMoment_bound (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) (k : Fin 2 → ℤ) :
    periodicFourierProbeMoment N a mass L ha hmass hL hperiod k ≤
      2 * (mass⁻¹ ^ 2 * L ^ 2) := by
  unfold periodicFourierProbeMoment
  have hc := physicalGJMeasure_periodicCosineTest_second_moment_le
    2 N a mass L ha hmass hL k hperiod
  have hs := physicalGJMeasure_periodicSineTest_second_moment_le
    2 N a mass L ha hmass hL k hperiod
  linarith
 theorem periodicHMinusTwo_lattice_probe_trace_bound (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) :
    Summable (fun k => periodicHMinusTwoWeight k *
      periodicFourierProbeMoment N a mass L ha hmass hL hperiod k) ∧
      ∑' k, periodicHMinusTwoWeight k *
        periodicFourierProbeMoment N a mass L ha hmass hL hperiod k ≤
        (2 * (mass⁻¹ ^ 2 * L ^ 2)) *
          ∑' k, periodicHMinusTwoWeight k := by
  apply periodicHMinusTwo_weighted_series_bound
  · exact periodicFourierProbeMoment_nonneg N a mass L ha hmass hL hperiod
  · exact periodicFourierProbeMoment_bound N a mass L ha hmass hL hperiod
  · positivity
end Pphi2Clean.Continuum
