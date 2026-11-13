import AImathPPhi2Clean.ArbitraryDimParameters
import AImathPPhi2Clean.RawAtomicGaussianTargetSpaceArbitraryDim
import AImathPPhi2Clean.PhysicalLatticeGaussianLaw
import Mathlib
import Mathlib.MeasureTheory.Measure.Map
set_option maxRecDepth 500000
set_option maxHeartbeats 0

noncomputable section
namespace Pphi2Clean.ArbitraryDimGaussian
open Pphi2Clean.ArbitraryDim
variable [Parameters]

open MeasureTheory ProbabilityTheory Filter Topology Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice

theorem measurable_actualTargetLift (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    Measurable (actualTargetLift N a L ha hL) := by
  unfold actualTargetLift
  have hcoords : Measurable (fun ξ : FiniteConfig N =>
      fun j : Fin (Fintype.card (FinLatticeSites dimension N)) =>
        ξ (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites dimension N)))) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites dimension N)))).comp (comap_measurable _)
  exact (continuous_targetCoefficientMap N a L ha).measurable.comp hcoords

def actualTargetGaussianMeasure (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) : Measure TargetCompletion :=
  Measure.map (actualTargetLift N a L ha hL)
    (finiteCovarianceGaussianMeasure
      (numberedLatticeCovarianceGJ dimension N a mass ha hmass))

instance actualTargetGaussianMeasure_isProbability (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) : IsProbabilityMeasure
      (actualTargetGaussianMeasure N a mass L ha hmass hL) := by
  unfold actualTargetGaussianMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_actualTargetLift N a L ha hL).aemeasurable).2 inferInstance

def actualTargetProbabilityMeasure (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) : ProbabilityMeasure TargetCompletion :=
  ⟨actualTargetGaussianMeasure N a mass L ha hmass hL, inferInstance⟩

def actualTargetProbabilityMeasure_fixedVolume
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    ProbabilityMeasure TargetCompletion :=
  actualTargetProbabilityMeasure (n + 1) (L / ((n + 1 : ℕ) : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL

theorem actualTargetLift_norm_sq (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L) (ξ : FiniteConfig N) (k : Index) :
    ‖actualTargetLift N a L ha hL ξ k‖ ^ 2 =
      targetWeight k * ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 := by
  rw [actualTargetLift_apply, norm_mul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt (targetWeight_nonneg k)]

theorem actualTargetGaussianMeasure_coordinate_second_moment (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) (k : Index) :
    (∫ x : TargetCompletion, ‖x k‖ ^ 2 ∂actualTargetGaussianMeasure N a mass L ha hmass hL) =
      targetWeight k * ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂
        finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ dimension N a mass ha hmass) := by
  have hc : Continuous (fun x : TargetCompletion => ‖x k‖ ^ 2) :=
    ((lp.evalCLM ℂ (fun _ : Index => ℂ) 2 k).continuous.norm).pow 2
  rw [actualTargetGaussianMeasure, integral_map
    (measurable_actualTargetLift N a L ha hL).aemeasurable hc.aestronglyMeasurable]
  simp_rw [actualTargetLift_norm_sq]
  exact integral_const_mul _ _

#print axioms actualTargetGaussianMeasure_coordinate_second_moment

theorem actualRawAtomicLift_integrable_sq (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) (k : Index) :
    Integrable (fun ξ => ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2)
      (finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ dimension N a mass ha hmass)) := by
  exact (rawFourierProbe_integrable_sq N a mass L ha hmass hL k).comp_measurable
    (latticeEmbedLift_measurable (physicalTestEval dimension N a))

theorem actualTargetGaussianMeasure_coordinate_integrable_sq (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) (k : Index) :
    Integrable (fun x : TargetCompletion => ‖x k‖ ^ 2)
      (actualTargetGaussianMeasure N a mass L ha hmass hL) := by
  have hc : Continuous (fun x : TargetCompletion => ‖x k‖ ^ 2) :=
    ((lp.evalCLM ℂ (fun _ : Index => ℂ) 2 k).continuous.norm).pow 2
  apply (integrable_map_measure hc.aestronglyMeasurable
    (measurable_actualTargetLift N a L ha hL).aemeasurable).2
  have hi := (actualRawAtomicLift_integrable_sq N a mass L ha hmass hL k).const_mul
    (targetWeight k)
  change Integrable (fun ξ => ‖actualTargetLift N a L ha hL ξ k‖ ^ 2) _
  simp_rw [actualTargetLift_norm_sq]
  exact hi

theorem actualTargetGaussianMeasure_integral_tail_eq (N R : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∫ x : TargetCompletion, ∑' k : Index,
      (if (R : ℝ) < ‖k‖ then ‖x k‖ ^ 2 else 0) ∂
        actualTargetGaussianMeasure N a mass L ha hmass hL) =
      actualExpectedTargetTail N R a mass L ha hmass hL := by
  let μ := actualTargetGaussianMeasure N a mass L ha hmass hL
  let C := 2 * (mass⁻¹ ^ 2 * L ^ dimension)
  let f : Index → TargetCompletion → ℝ :=
    fun k x => if (R : ℝ) < ‖k‖ then ‖x k‖ ^ 2 else 0
  have hf0 (k : Index) (x : TargetCompletion) : 0 ≤ f k x := by
    dsimp [f]
    split_ifs <;> positivity
  have hi (k : Index) : Integrable (f k) μ := by
    dsimp [f]
    split_ifs
    · exact actualTargetGaussianMeasure_coordinate_integrable_sq N a mass L ha hmass hL k
    · exact integrable_zero TargetCompletion ℝ μ
  have heq (k : Index) : (∫ x, f k x ∂μ) =
      (if (R : ℝ) < ‖k‖ then targetWeight k else 0) *
        ∫ ξ, ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2 ∂
          finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ dimension N a mass ha hmass) := by
    dsimp [f]
    split_ifs
    · exact actualTargetGaussianMeasure_coordinate_second_moment N a mass L ha hmass hL k
    · simp
  have hm : Summable (fun k : Index => targetWeight k * C) := by
    have hw : Summable targetWeight := Pphi2Clean.ArbitraryDim.target_weight_summable
    exact hw.mul_right C
  have hb (k : Index) : (∫ x, f k x ∂μ) ≤ targetWeight k * C := by
    rw [heq]
    split_ifs
    · exact mul_le_mul_of_nonneg_left
        (actualRawAtomicLift_integral_norm_sq_le N a mass L ha hmass hvol hL k)
        (targetWeight_nonneg k)
    · simp only [zero_mul]
      exact mul_nonneg (targetWeight_nonneg k) (by dsimp [C]; positivity)
  have hs : Summable (fun k => ∫ x, f k x ∂μ) :=
    hm.of_nonneg_of_le (fun k => integral_nonneg (hf0 k)) hb
  have hsn : Summable (fun k => ∫ x, ‖f k x‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _ _)] using hs
  have hswap := integral_tsum_of_summable_integral_norm hi hsn
  change (∫ x, ∑' k, f k x ∂μ) = _
  rw [← hswap]
  unfold actualExpectedTargetTail
  exact tsum_congr heq

#print axioms actualTargetGaussianMeasure_integral_tail_eq

theorem actualExpectedTargetTail_nonneg (N R : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) :
    0 ≤ actualExpectedTargetTail N R a mass L ha hmass hL := by
  unfold actualExpectedTargetTail
  apply tsum_nonneg
  intro k
  apply mul_nonneg
  · by_cases hk : (R : ℝ) < ‖k‖
    · simp [hk, targetWeight_nonneg]
    · simp [hk]
  · exact integral_nonneg (fun ξ => sq_nonneg _)

theorem actualExpectedTargetTail_fixedVolume_tendsto_zero
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    Filter.Tendsto
      (fun R : ℕ => actualExpectedTargetTail (n + 1)
        R (L / ((n + 1 : ℕ) : ℝ)) mass L
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL)
      atTop (𝓝 0) := by
  let C : ℝ := 2 * (mass⁻¹ ^ 2 * L ^ dimension) * ∑' k : Index, energyWeight k
  have hC : 0 ≤ C := by
    dsimp [C]
    apply mul_nonneg
    · positivity
    · apply tsum_nonneg
      intro k
      exact energyWeight_nonneg k
  have hpow : Filter.Tendsto
      (fun R : ℕ => ((1 + (R : ℝ)) ^ (-(2 * gap)))) atTop (𝓝 0) := by
    have hshift : Filter.Tendsto (fun R : ℕ => ((R + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    convert (tendsto_rpow_neg_atTop (mul_pos (by norm_num) gap_positive : (0 : ℝ) < 2 * gap)).comp hshift using 1
    · funext R
      change (1 + (R : ℝ)) ^ (-(2 * gap)) = ((R + 1 : ℕ) : ℝ) ^ (-(2 * gap))
      exact congrArg (fun x : ℝ => x ^ (-(2 * gap)))
        (by simp only [Nat.cast_add, Nat.cast_one]; exact add_comm _ _)
  have hup : Filter.Tendsto (fun R : ℕ => ((1 + (R : ℝ)) ^ (-(2 * gap))) * C)
      atTop (𝓝 0) := by
    simpa [mul_zero] using hpow.mul_const C
  apply squeeze_zero
  · intro R
    exact actualExpectedTargetTail_nonneg (n + 1) R
      (L / ((n + 1 : ℕ) : ℝ)) mass L
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL
  · intro R
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.succ_pos n)
    have hvol : L / ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) = L :=
      div_mul_cancel₀ L (ne_of_gt hN)
    exact actualExpectedTargetTail_le (n + 1) R
      (L / ((n + 1 : ℕ) : ℝ)) mass L
      (div_pos hL hN) hmass hvol hL
  · simpa [C, mul_assoc, mul_left_comm, mul_comm] using hup

theorem actualExpectedTargetTail_fixedVolume_uniform
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ n : ℕ,
      actualExpectedTargetTail (n + 1) R (L / ((n + 1 : ℕ) : ℝ)) mass L
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL < ε := by
  let C : ℝ := 2 * (mass⁻¹ ^ 2 * L ^ dimension) * ∑' k : Index, energyWeight k
  have hshift : Tendsto (fun R : ℕ => ((R + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hp : Tendsto (fun R : ℕ => (1 + (R : ℝ)) ^ (-(2 * gap))) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (mul_pos (by norm_num) gap_positive : (0 : ℝ) < 2 * gap)).comp hshift using 1
    funext R
    change (1 + (R : ℝ)) ^ (-(2 * gap)) = ((R + 1 : ℕ) : ℝ) ^ (-(2 * gap))
    exact congrArg (fun x : ℝ => x ^ (-(2 * gap)))
      (by simp only [Nat.cast_add, Nat.cast_one]; exact add_comm _ _)
  have hb : Tendsto (fun R : ℕ => (1 + (R : ℝ)) ^ (-(2 * gap)) * C) atTop (𝓝 0) := by
    simpa using hp.mul_const C
  obtain ⟨R, hR⟩ := (hb.eventually (Iio_mem_nhds hε)).exists
  refine ⟨R, fun n => lt_of_le_of_lt ?_ hR⟩
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  exact actualExpectedTargetTail_le (n + 1) R (L / ((n + 1 : ℕ) : ℝ)) mass L
    (div_pos hL hN) hmass (div_mul_cancel₀ L (ne_of_gt hN)) hL

#print axioms actualExpectedTargetTail_fixedVolume_uniform

#check actualTargetProbabilityMeasure_fixedVolume
#check actualExpectedTargetTail_fixedVolume_tendsto_zero
#print axioms actualExpectedTargetTail_fixedVolume_tendsto_zero

theorem actualTargetGaussianMeasure_apply (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) (s : Set TargetCompletion) (hs : MeasurableSet s) :
    actualTargetGaussianMeasure N a mass L ha hmass hL s =
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ dimension N a mass ha hmass)
        ((actualTargetLift N a L ha hL) ⁻¹' s) := by
  rw [actualTargetGaussianMeasure]
  exact Measure.map_apply
    (measurable_actualTargetLift N a L ha hL) hs

#print axioms actualTargetGaussianMeasure_isProbability
#print axioms actualTargetGaussianMeasure_apply

end Pphi2Clean.ArbitraryDimGaussian
