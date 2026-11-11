import AImathPPhi2Clean.Periodic3DCarrierEnergy
import AImathPPhi2Clean.Periodic3DHminusTwoProbeTrace

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

theorem periodic3DRawAtomicLift_integral_tsum_hminusTwo
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∑' k : Periodic3DIndex, ∫ ω,
      periodic3DHminusTwoWeight k * ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) =
    ∫ ω, ∑' k : Periodic3DIndex,
      periodic3DHminusTwoWeight k * ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass) := by
  let T := numberedLatticeCovarianceGJ 3 N a mass ha hmass
  apply integral_tsum_of_summable_integral_norm
  · intro k
    let fc := latticeTestField (physicalTestEval 3 N a) (periodicCosineTest 3 L k hL)
    let fs := latticeTestField (physicalTestEval 3 N a) (periodicSineTest 3 L k hL)
    have hc := (finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T fc).memLp_two.integrable_sq
    have hs := (finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T fs).memLp_two.integrable_sq
    have hp : Integrable (fun ω => ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2)
        (finiteCovarianceGaussianMeasure T) := by
      apply (hc.add hs).congr
      filter_upwards [] with ω
      change (ω fc) ^ 2 + (ω fs) ^ 2 = _
      change _ = ‖periodic3DComplexFourierProbe L hL k
        (latticeEmbedLift (physicalTestEval 3 N a) ω)‖ ^ 2
      rw [periodic3DComplexFourierProbe_norm_sq, latticeEmbedLift_eval_eq, latticeEmbedLift_eval_eq]
    exact hp.const_mul _
  · have ht :=
      (periodic3DComplexFourierProbe_hminusTwo_weighted_trace_bound
        N a mass L ha hmass hvol hL).1
    apply ht.congr
    intro k
    rw [← periodic3DRawAtomicLift_integral_norm_sq_eq_probeMoment
      N a mass L ha hmass hL k]
    rw [← integral_const_mul]
    congr 1
    funext ω
    exact ((Real.norm_eq_abs _).trans (abs_of_nonneg
      (mul_nonneg (periodic3DSobolevWeight_nonneg 2 k) (sq_nonneg _)))).symm

theorem periodic3DRawAtomicLift_integral_energy_hminusTwo_le
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∫ ω, ∑' k : Periodic3DIndex,
      periodic3DHminusTwoWeight k * ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) ≤
      2 * (mass⁻¹ ^ 2 * L ^ 3) * ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k := by
  rw [← periodic3DRawAtomicLift_integral_tsum_hminusTwo
    N a mass L ha hmass hvol hL]
  calc
    _ = ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k *
        periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k := by
      apply tsum_congr
      intro k
      rw [integral_const_mul,
        periodic3DRawAtomicLift_integral_norm_sq_eq_probeMoment N a mass L ha hmass hL k]
    _ ≤ _ := (periodic3DComplexFourierProbe_hminusTwo_weighted_trace_bound
      N a mass L ha hmass hvol hL).2

end Pphi2Clean.Continuum
