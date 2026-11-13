import AImathPPhi2Clean.ArbitraryDimParameters
import AImathPPhi2Clean.PhysicalLatticeGaussianLaw
import AImathPPhi2Clean.RealFourierSecondMoment
import AImathPPhi2Clean.DimensionFreeWeightSummability
import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false
noncomputable section
namespace Pphi2Clean.ArbitraryDimGaussian
open Pphi2Clean.ArbitraryDim
variable [Parameters]
open MeasureTheory ProbabilityTheory Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice
abbrev Index := Fin dimension → ℤ
abbrev Configuration := WeakDual ℝ (BoundedContinuousFunction (Fin dimension → ℝ) ℝ)
def energyWeight (k : Index) : ℝ := (1 + ‖k‖) ^ (-2 * energyOrder)
lemma energyWeight_nonneg (k : Index) : 0 ≤ energyWeight k := by
  unfold energyWeight
  exact Real.rpow_nonneg (by positivity) _
def rawFourierProbe (L : ℝ) (hL : 0 < L) (k : Index)
    (ω : Configuration) : ℂ :=
  (ω (periodicCosineTest dimension L k hL) : ℂ) +
    (ω (periodicSineTest dimension L k hL) : ℂ) * Complex.I
theorem rawFourierProbe_norm_sq (L : ℝ) (hL : 0 < L) (k : Index)
    (ω : Configuration) :
    ‖rawFourierProbe L hL k ω‖ ^ 2 =
      (ω (periodicCosineTest dimension L k hL)) ^ 2 +
        (ω (periodicSineTest dimension L k hL)) ^ 2 := by
  unfold rawFourierProbe
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]
def rawFourierProbeMoment (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) (k : Index) : ℝ :=
  ∫ ω, ‖rawFourierProbe L hL k ω‖ ^ 2 ∂
    physicalGJMeasure dimension N a mass ha hmass
theorem rawFourierProbeMoment_le (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) (k : Index) :
    rawFourierProbeMoment N a mass L ha hmass hL k ≤
      2 * (mass⁻¹ ^ 2 * L ^ dimension) := by
  unfold rawFourierProbeMoment
  let μ := physicalGJMeasure dimension N a mass ha hmass
  have hcosLaw := physicalGJMeasure_eval_hasGaussianLaw dimension N a mass ha hmass
    (periodicCosineTest dimension L k hL)
  have hsinLaw := physicalGJMeasure_eval_hasGaussianLaw dimension N a mass ha hmass
    (periodicSineTest dimension L k hL)
  have hcosInt : Integrable (fun ω => (ω (periodicCosineTest dimension L k hL)) ^ 2) μ := hcosLaw.memLp_two.integrable_sq
  have hsinInt : Integrable (fun ω => (ω (periodicSineTest dimension L k hL)) ^ 2) μ := hsinLaw.memLp_two.integrable_sq
  have hcos := physicalGJMeasure_periodicCosineTest_second_moment_le dimension N a mass L ha hmass hvol k hL
  have hsin := physicalGJMeasure_periodicSineTest_second_moment_le dimension N a mass L ha hmass hvol k hL
  calc
    (∫ ω, ‖rawFourierProbe L hL k ω‖ ^ 2 ∂μ) =
        ∫ ω, (ω (periodicCosineTest dimension L k hL)) ^ 2 + (ω (periodicSineTest dimension L k hL)) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact rawFourierProbe_norm_sq L hL k ω
    _ = (∫ ω, (ω (periodicCosineTest dimension L k hL)) ^ 2 ∂μ) +
        ∫ ω, (ω (periodicSineTest dimension L k hL)) ^ 2 ∂μ := integral_add hcosInt hsinInt
    _ ≤ mass⁻¹ ^ 2 * L ^ dimension + mass⁻¹ ^ 2 * L ^ dimension := add_le_add hcos hsin
    _ = 2 * (mass⁻¹ ^ 2 * L ^ dimension) := by ring
theorem rawFourierProbe_integrable_sq (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) (k : Index) :
    Integrable (fun ω => ‖rawFourierProbe L hL k ω‖ ^ 2)
      (physicalGJMeasure dimension N a mass ha hmass) := by
  let μ := physicalGJMeasure dimension N a mass ha hmass
  have hcosLaw := physicalGJMeasure_eval_hasGaussianLaw dimension N a mass ha hmass (periodicCosineTest dimension L k hL)
  have hsinLaw := physicalGJMeasure_eval_hasGaussianLaw dimension N a mass ha hmass (periodicSineTest dimension L k hL)
  have hc := hcosLaw.memLp_two.integrable_sq
  have hs := hsinLaw.memLp_two.integrable_sq
  apply (hc.add hs).congr
  filter_upwards [] with ω
  exact (rawFourierProbe_norm_sq L hL k ω).symm
def expectedRawEnergy (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) : ℝ :=
  ∫ ω, ∑' k : Index, energyWeight k * ‖rawFourierProbe L hL k ω‖ ^ 2 ∂
    physicalGJMeasure dimension N a mass ha hmass
theorem expectedRawEnergy_le (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    expectedRawEnergy N a mass L ha hmass hL ≤
      2 * (mass⁻¹ ^ 2 * L ^ dimension) * ∑' k : Index, energyWeight k := by
  unfold expectedRawEnergy
  let μ := physicalGJMeasure dimension N a mass ha hmass
  let C := 2 * (mass⁻¹ ^ 2 * L ^ dimension)
  have hw : Summable energyWeight := by
    unfold energyWeight
    exact Pphi2Clean.ArbitraryDim.energy_weight_summable
  have hs : Summable (fun k : Index => energyWeight k * C) := hw.mul_right C
  have hi (k : Index) := (rawFourierProbe_integrable_sq N a mass L ha hmass hL k).const_mul (energyWeight k)
  have hb (k : Index) :
      ∫ ω, energyWeight k * ‖rawFourierProbe L hL k ω‖ ^ 2 ∂μ ≤ energyWeight k * C := by
    rw [integral_const_mul]
    unfold C
    exact mul_le_mul_of_nonneg_left (rawFourierProbeMoment_le N a mass L ha hmass hvol hL k) (energyWeight_nonneg k)
  have hn (k : Index) :
      0 ≤ ∫ ω, energyWeight k * ‖rawFourierProbe L hL k ω‖ ^ 2 ∂μ :=
    integral_nonneg (fun ω => mul_nonneg (energyWeight_nonneg k) (sq_nonneg _))
  have ht := hs.of_nonneg_of_le hn hb
  have heq := integral_tsum_of_summable_integral_norm hi (by
    apply ht.congr
    intro k
    congr 1
    funext ω
    exact (abs_of_nonneg (mul_nonneg (energyWeight_nonneg k) (sq_nonneg _))).symm)
  rw [← heq]
  calc
    _ ≤ ∑' k : Index, energyWeight k * C := ht.tsum_le_tsum hb hs
    _ = C * ∑' k : Index, energyWeight k := by rw [tsum_mul_right]; ring
#print axioms rawFourierProbeMoment_le
#print axioms expectedRawEnergy_le
end Pphi2Clean.ArbitraryDimGaussian
