import AImathPPhi2Clean.RawAtomicGaussian122409
import AImathPPhi2Clean.TailRatio
import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false
noncomputable section
namespace Pphi2Clean.Dim122409Gaussian
open MeasureTheory ProbabilityTheory Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice
def targetWeight (k : Index) : ℝ := (1 + ‖k‖) ^ (-2 * (61206 : ℝ))
def actualExpectedTargetTail (N R : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) : ℝ :=
  ∑' k : Index, (if (R : ℝ) < ‖k‖ then targetWeight k else 0) *
    ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 122409 N a mass ha hmass)
theorem actualExpectedTargetTail_le (N R : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    actualExpectedTargetTail N R a mass L ha hmass hL ≤
      (1 + (R : ℝ)) ^ (-2 : ℝ) *
        (2 * (mass⁻¹ ^ 2 * L ^ 122409) * ∑' k : Index, energyWeight k) := by
  let C := 2 * (mass⁻¹ ^ 2 * L ^ 122409)
  let q := (1 + (R : ℝ)) ^ (-2 : ℝ)
  let μ := finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 122409 N a mass ha hmass)
  have hw : Summable energyWeight := by
    unfold energyWeight
    exact Pphi2Clean.DimensionFreeProbe.energy_weight_summable
  have hmajor : Summable (fun k : Index => q * (energyWeight k * C)) :=
    (hw.mul_right C).mul_left q
  have hq : 0 ≤ q := by dsimp [q]; exact Real.rpow_nonneg (by positivity) _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hw0 := fun k => energyWeight_nonneg k
  have hterm (k : Index) :
      (if (R : ℝ) < ‖k‖ then targetWeight k else 0) *
        ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂μ ≤ q * (energyWeight k * C) := by
    by_cases hk : (R : ℝ) < ‖k‖
    · have hratio := Pphi2Clean.DimensionFreeProbe.target_fourier_term_le_radius_factor k R (le_of_lt hk)
      rw [if_pos hk]
      calc
        targetWeight k * (∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂μ)
            ≤ q * energyWeight k * (∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂μ) :=
              mul_le_mul_of_nonneg_right (by simpa [targetWeight, energyWeight, q] using hratio)
                (integral_nonneg (fun ξ => sq_nonneg _))
        _ ≤ q * energyWeight k * C := mul_le_mul_of_nonneg_left
              (actualRawAtomicLift_integral_norm_sq_le N a mass L ha hmass hvol hL k)
              (mul_nonneg hq (hw0 k))
        _ = q * (energyWeight k * C) := by ring
    · rw [if_neg hk]
      have hn : 0 ≤ q * (energyWeight k * C) := mul_nonneg hq (mul_nonneg (hw0 k) hC)
      simpa using hn
  have hnonneg (k : Index) :
      0 ≤ (if (R : ℝ) < ‖k‖ then targetWeight k else 0) *
        ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂μ := by
    by_cases hk : (R : ℝ) < ‖k‖
    · rw [if_pos hk]
      apply mul_nonneg
      · unfold targetWeight
        have hb : 0 ≤ 1 + ‖k‖ := by linarith [norm_nonneg k]
        exact Real.rpow_nonneg hb _
      · exact integral_nonneg (fun ξ => sq_nonneg _)
    · simp [hk]
  have hsum := Summable.of_nonneg_of_le hnonneg hterm hmajor
  have htsum := hsum.tsum_le_tsum hterm hmajor
  unfold actualExpectedTargetTail
  calc
    _ ≤ ∑' k : Index, q * (energyWeight k * C) := htsum
    _ = q * (C * ∑' k : Index, energyWeight k) := by rw [tsum_mul_left, tsum_mul_right]; ring
#print axioms actualExpectedTargetTail_le
end Pphi2Clean.Dim122409Gaussian
