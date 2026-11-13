import AImathPPhi2Clean.ArbitraryDimParameters
import AImathPPhi2Clean.GaussianModeArbitraryDim
import AImathPPhi2Clean.LatticeGaussianContinuumConsumer
import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false
noncomputable section
namespace Pphi2Clean.ArbitraryDimGaussian
open Pphi2Clean.ArbitraryDim
variable [Parameters]
open MeasureTheory ProbabilityTheory Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice
abbrev FiniteConfig (N : ℕ) [NeZero N] :=
  FiniteLatticeConfiguration (Fintype.card (FinLatticeSites dimension N))
def actualRawAtomicLift (N : ℕ) [NeZero N] (a L : ℝ) (hL : 0 < L) :
    FiniteConfig N → Index → ℂ :=
  fun ξ k => rawFourierProbe L hL k
    (latticeEmbedLift (physicalTestEval dimension N a) ξ)
theorem actualRawAtomicLift_integral_norm_sq_eq_moment (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) (k : Index) :
    ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ dimension N a mass ha hmass) =
      rawFourierProbeMoment N a mass L ha hmass hL k := by
  let μ := physicalGJMeasure dimension N a mass ha hmass
  have hprobe := rawFourierProbe_integrable_sq N a mass L ha hmass hL k
  have hmap := integral_map
    (latticeEmbedLift_measurable (physicalTestEval dimension N a)).aemeasurable
    hprobe.aestronglyMeasurable
  change (∫ ξ, ‖rawFourierProbe L hL k
      (latticeEmbedLift (physicalTestEval dimension N a) ξ)‖ ^ 2 ∂
        finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ dimension N a mass ha hmass)) = _
  rw [← hmap]
  rfl
theorem actualRawAtomicLift_integral_norm_sq_le (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) (k : Index) :
    ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ dimension N a mass ha hmass) ≤
      2 * (mass⁻¹ ^ 2 * L ^ dimension) := by
  rw [actualRawAtomicLift_integral_norm_sq_eq_moment]
  exact rawFourierProbeMoment_le N a mass L ha hmass hvol hL k

def actualExpectedRawEnergy (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) : ℝ :=
  ∑' k : Index, energyWeight k *
    ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ dimension N a mass ha hmass)
theorem actualExpectedRawEnergy_le (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    actualExpectedRawEnergy N a mass L ha hmass hL ≤
      2 * (mass⁻¹ ^ 2 * L ^ dimension) * ∑' k : Index, energyWeight k := by
  let C := 2 * (mass⁻¹ ^ 2 * L ^ dimension)
  let μ := finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ dimension N a mass ha hmass)
  have hw : Summable energyWeight := by
    unfold energyWeight
    exact Pphi2Clean.ArbitraryDim.energy_weight_summable
  have hs : Summable (fun k : Index => energyWeight k * C) := hw.mul_right C
  have hn (k : Index) :
      0 ≤ ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂μ :=
    integral_nonneg (fun ξ => sq_nonneg _)
  have hb (k : Index) :
      energyWeight k * ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂μ ≤
        energyWeight k * C :=
    mul_le_mul_of_nonneg_left
      (actualRawAtomicLift_integral_norm_sq_le N a mass L ha hmass hvol hL k)
      (energyWeight_nonneg k)
  have ht := hs.of_nonneg_of_le
    (fun k => mul_nonneg (energyWeight_nonneg k) (hn k)) hb
  unfold actualExpectedRawEnergy
  calc
    _ ≤ ∑' k : Index, energyWeight k * C := ht.tsum_le_tsum hb hs
    _ = C * ∑' k : Index, energyWeight k := by rw [tsum_mul_right]; ring
#print axioms actualRawAtomicLift_integral_norm_sq_le
#print axioms actualExpectedRawEnergy_le
end Pphi2Clean.ArbitraryDimGaussian
