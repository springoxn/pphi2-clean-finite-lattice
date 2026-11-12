import AImathPPhi2Clean.ActualTargetGaussianMeasure122409
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import AImathPPhi2Clean.FiniteFrequencyBall

set_option maxRecDepth 500000
set_option maxHeartbeats 0
noncomputable section
namespace Pphi2Clean.Dim122409Gaussian
open MeasureTheory ProbabilityTheory Filter Topology

/-- The canonical finite-coordinate approximation in the weighted target space. -/
def targetTruncation (s : Finset Index) (x : TargetCompletion) : TargetCompletion :=
  ∑ k ∈ s, lp.single 2 k (x k)

theorem continuous_targetTruncation (s : Finset Index) :
    Continuous (targetTruncation s) := by
  classical
  unfold targetTruncation
  apply continuous_finsetSum
  intro k hk
  exact (lp.singleContinuousLinearMap ℂ (fun _ : Index => ℂ) 2 k).continuous.comp
    (lp.evalCLM ℂ (fun _ : Index => ℂ) 2 k).continuous

theorem targetTruncation_apply (s : Finset Index) (x : TargetCompletion) (k : Index) :
    targetTruncation s x k = if k ∈ s then x k else 0 := by
  classical
  simp only [targetTruncation, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

theorem targetTruncation_tail_norm_sq (s : Finset Index) (x : TargetCompletion) :
    ‖x - targetTruncation s x‖ ^ 2 =
      ∑' k : Index, if k ∈ s then 0 else ‖x k‖ ^ 2 := by
  classical
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
    (x - targetTruncation s x)
  have hn' : ‖x - targetTruncation s x‖ ^ 2 =
      ∑' k : Index, ‖(x - targetTruncation s x) k‖ ^ 2 := by
    simpa using hn
  rw [hn']
  apply tsum_congr
  intro k
  rw [lp.coeFn_sub, Pi.sub_apply, targetTruncation_apply]
  split_ifs <;> simp_all

def targetFrequencySet (R : ℕ) : Finset Index :=
  (Pphi2Clean.DimensionFreeProbe.finite_frequency_ball 122409 R).toFinset

@[simp] theorem mem_targetFrequencySet (R : ℕ) (k : Index) :
    k ∈ targetFrequencySet R ↔ ‖k‖ ≤ (R : ℝ) := by
  simp [targetFrequencySet]

theorem targetFrequency_tail_norm_sq (R : ℕ) (x : TargetCompletion) :
    ‖x - targetTruncation (targetFrequencySet R) x‖ ^ 2 =
      ∑' k : Index, if (R : ℝ) < ‖k‖ then ‖x k‖ ^ 2 else 0 := by
  rw [targetTruncation_tail_norm_sq]
  apply tsum_congr
  intro k
  by_cases hk : ‖k‖ ≤ (R : ℝ)
  · simp [hk, not_lt.mpr hk]
  · simp [hk, lt_of_not_ge hk]

theorem actualTargetGaussianMeasure_integral_truncation_error (N R : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∫ x : TargetCompletion,
      ‖x - targetTruncation (targetFrequencySet R) x‖ ^ 2 ∂
        actualTargetGaussianMeasure N a mass L ha hmass hL) =
      actualExpectedTargetTail N R a mass L ha hmass hL := by
  simp_rw [targetFrequency_tail_norm_sq]
  exact actualTargetGaussianMeasure_integral_tail_eq N R a mass L ha hmass hvol hL

def targetHeadMap (s : Finset Index) (c : (↑s : Type) → ℂ) : TargetCompletion :=
  ∑ k : s, lp.single 2 k (c k)

theorem continuous_targetHeadMap (s : Finset Index) : Continuous (targetHeadMap s) := by
  classical
  unfold targetHeadMap
  apply continuous_finsetSum
  intro k hk
  exact (lp.singleContinuousLinearMap ℂ (fun _ : Index => ℂ) 2 k).continuous.comp
    (continuous_apply k)

theorem targetHeadMap_restrict (s : Finset Index) (x : TargetCompletion) :
    targetHeadMap s (fun k : s => x k) = targetTruncation s x := by
  classical
  simp [targetHeadMap, targetTruncation]

theorem targetTruncation_compact_head (s : Finset Index) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : Set TargetCompletion, IsCompact C ∧
      ∀ x : TargetCompletion, ‖x‖ ≤ M → targetTruncation s x ∈ C := by
  classical
  let C := targetHeadMap s '' Metric.closedBall (0 : s → ℂ) M
  refine ⟨C, (isCompact_closedBall _ _).image (continuous_targetHeadMap s), ?_⟩
  intro x hx
  refine ⟨(fun k : s => x k), ?_, targetHeadMap_restrict s x⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hM).2
  intro k
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x k).trans hx

/-- Compact approximation at every metric scale gives total boundedness. -/
theorem target_totallyBounded_of_compact_approximation (K : Set TargetCompletion)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : Set TargetCompletion, IsCompact C ∧
      ∀ x ∈ K, ∃ y ∈ C, dist x y < ε) : TotallyBounded K := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨C, hC, hclose⟩ := h (ε / 2) (by positivity)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hC.totallyBounded
    (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hclose x hx
  have hycov := hcover hy
  simp only [Set.mem_iUnion, Metric.mem_ball] at hycov ⊢
  obtain ⟨z, hz, hyz⟩ := hycov
  refine ⟨z, hz, ?_⟩
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy hyz
    _ = ε := by ring

theorem target_isCompact_of_uniform_truncation (K : Set TargetCompletion)
    (hclosed : IsClosed K) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ M)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ s : Finset Index,
      ∀ x ∈ K, ‖x - targetTruncation s x‖ < ε) : IsCompact K := by
  apply TotallyBounded.isCompact_of_isClosed _ hclosed
  apply target_totallyBounded_of_compact_approximation
  intro ε hε
  obtain ⟨s, hs⟩ := htail ε hε
  obtain ⟨C, hC, hhead⟩ := targetTruncation_compact_head s M hM
  refine ⟨C, hC, ?_⟩
  intro x hx
  exact ⟨targetTruncation s x, hhead x (hbound x hx), by
    simpa only [dist_eq_norm] using hs x hx⟩

def targetEnergyBall (M : ℝ) : Set TargetCompletion :=
  {x | ∀ s : Finset Index, ∑ k ∈ s, (1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2 ≤ M}

theorem targetEnergyBall_summable (M : ℝ) (x : TargetCompletion)
    (hx : x ∈ targetEnergyBall M) :
    Summable (fun k : Index => (1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2) :=
  summable_of_sum_le (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hx

theorem targetEnergyBall_tsum_le (M : ℝ) (x : TargetCompletion)
    (hx : x ∈ targetEnergyBall M) :
    (∑' k : Index, (1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2) ≤ M :=
  (targetEnergyBall_summable M x hx).tsum_le_of_sum_le hx

theorem isClosed_targetEnergyBall (M : ℝ) : IsClosed (targetEnergyBall M) := by
  have heq : targetEnergyBall M = ⋂ s : Finset Index,
      {x : TargetCompletion | ∑ k ∈ s, (1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2 ≤ M} := by
    ext x
    simp [targetEnergyBall]
  rw [heq]
  apply isClosed_iInter
  intro s
  apply isClosed_le _ continuous_const
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul (((lp.evalCLM ℂ (fun _ : Index => ℂ) 2 k).continuous.norm).pow 2)

theorem targetEnergyBall_norm_sq_le (M : ℝ) (x : TargetCompletion)
    (hx : x ∈ targetEnergyBall M) : ‖x‖ ^ 2 ≤ M := by
  have hn : ‖x‖ ^ 2 = ∑' k : Index, ‖x k‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x
  have hle (k : Index) : ‖x k‖ ^ 2 ≤ (1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2 := by
    nlinarith [norm_nonneg k, sq_nonneg ‖k‖, sq_nonneg ‖x k‖]
  rw [hn]
  exact ((targetEnergyBall_summable M x hx).of_nonneg_of_le
    (fun k => sq_nonneg _) hle).tsum_le_tsum hle
      (targetEnergyBall_summable M x hx) |>.trans (targetEnergyBall_tsum_le M x hx)

theorem targetEnergyBall_tail_sq_le (M : ℝ) (x : TargetCompletion)
    (hx : x ∈ targetEnergyBall M) (R : ℕ) :
    ‖x - targetTruncation (targetFrequencySet R) x‖ ^ 2 ≤
      (1 + (R : ℝ)) ^ (-2 : ℝ) * M := by
  have hq : 0 ≤ (1 + (R : ℝ)) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hpoint (k : Index) : (if (R : ℝ) < ‖k‖ then ‖x k‖ ^ 2 else 0) ≤
      (1 + (R : ℝ)) ^ (-2 : ℝ) * ((1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2) := by
    split_ifs with hk
    · have hp : (1 + (R : ℝ)) ^ 2 ≤ (1 + ‖k‖) ^ 2 := by
        nlinarith [norm_nonneg k, (Nat.cast_nonneg R : (0 : ℝ) ≤ (R : ℝ))]
      have hbase : 0 < (1 + (R : ℝ)) ^ 2 := by positivity
      have hrat : (1 : ℝ) ≤ ((1 + (R : ℝ)) ^ 2)⁻¹ * (1 + ‖k‖) ^ 2 := by
        rw [← div_eq_inv_mul, le_div_iff₀ hbase]
        simpa using hp
      have hpow : (1 + (R : ℝ)) ^ (-2 : ℝ) = ((1 + (R : ℝ)) ^ 2)⁻¹ := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two]
      rw [hpow]
      nlinarith [sq_nonneg ‖x k‖]
    · exact mul_nonneg hq (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs := (targetEnergyBall_summable M x hx).mul_left
    ((1 + (R : ℝ)) ^ (-2 : ℝ))
  have ht := hs.of_nonneg_of_le (fun k => by split_ifs <;> positivity) hpoint
  rw [targetFrequency_tail_norm_sq]
  calc
    _ ≤ ∑' k : Index, (1 + (R : ℝ)) ^ (-2 : ℝ) *
        ((1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2) := ht.tsum_le_tsum hpoint hs
    _ = (1 + (R : ℝ)) ^ (-2 : ℝ) *
        ∑' k : Index, (1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2 := tsum_mul_left
    _ ≤ (1 + (R : ℝ)) ^ (-2 : ℝ) * M :=
      mul_le_mul_of_nonneg_left (targetEnergyBall_tsum_le M x hx) hq

theorem isCompact_targetEnergyBall (M : ℝ) (hM : 0 ≤ M) :
    IsCompact (targetEnergyBall M) := by
  apply target_isCompact_of_uniform_truncation _ (isClosed_targetEnergyBall M)
    (Real.sqrt M) (Real.sqrt_nonneg M)
  · intro x hx
    exact (Real.le_sqrt (norm_nonneg _) hM).2 (targetEnergyBall_norm_sq_le M x hx)
  · intro ε hε
    have hshift : Tendsto (fun R : ℕ => ((R + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    have hp : Tendsto (fun R : ℕ => (1 + (R : ℝ)) ^ (-2 : ℝ)) atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp hshift using 1
      funext R
      change (1 + (R : ℝ)) ^ (-2 : ℝ) = ((R + 1 : ℕ) : ℝ) ^ (-2 : ℝ)
      exact congrArg (fun y : ℝ => y ^ (-2 : ℝ))
        (by simp only [Nat.cast_add, Nat.cast_one]; exact add_comm _ _)
    have hb : Tendsto (fun R : ℕ => (1 + (R : ℝ)) ^ (-2 : ℝ) * M) atTop (𝓝 0) := by
      simpa using hp.mul_const M
    obtain ⟨R, hR⟩ := (hb.eventually (Iio_mem_nhds (sq_pos_of_pos hε))).exists
    refine ⟨targetFrequencySet R, fun x hx => ?_⟩
    have hsq := lt_of_le_of_lt (targetEnergyBall_tail_sq_le M x hx R) hR
    nlinarith [norm_nonneg (x - targetTruncation (targetFrequencySet R) x)]

def targetSourceEnergy (x : TargetCompletion) : ENNReal :=
  ∑' k : Index, ENNReal.ofReal ((1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2)

theorem measurable_targetSourceEnergy : Measurable targetSourceEnergy := by
  apply Measurable.tsum
  intro k
  exact ENNReal.measurable_ofReal.comp (continuous_const.mul
    (((lp.evalCLM ℂ (fun _ : Index => ℂ) 2 k).continuous.norm).pow 2)).measurable

theorem targetSourceEnergy_le_mem (x : TargetCompletion) (M : ℝ)
    (hM : 0 ≤ M) (hx : targetSourceEnergy x ≤ ENNReal.ofReal M) :
    x ∈ targetEnergyBall M := by
  intro s
  have hn (k : Index) : 0 ≤ (1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  apply (ENNReal.ofReal_le_ofReal_iff hM).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => hn k)]
  exact (ENNReal.sum_le_tsum s).trans hx

theorem target_source_weight_identity (k : Index) :
    (1 + ‖k‖) ^ 2 * targetWeight k = energyWeight k := by
  have hp : 0 < 1 + ‖k‖ := by positivity
  unfold targetWeight energyWeight
  rw [← Real.rpow_two, ← Real.rpow_add hp]
  congr 1
  norm_num

theorem actualTargetGaussianMeasure_sourceEnergy_bound (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∫⁻ x, targetSourceEnergy x ∂actualTargetGaussianMeasure N a mass L ha hmass hL) ≤
      ENNReal.ofReal (2 * (mass⁻¹ ^ 2 * L ^ 122409) * ∑' k : Index, energyWeight k) := by
  let μ := actualTargetGaussianMeasure N a mass L ha hmass hL
  let C := 2 * (mass⁻¹ ^ 2 * L ^ 122409)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm (k : Index) : (∫⁻ x, ENNReal.ofReal ((1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal (energyWeight k * C) := by
    have hi := (actualTargetGaussianMeasure_coordinate_integrable_sq N a mass L ha hmass hL k).const_mul
      ((1 + ‖k‖) ^ 2)
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
    apply ENNReal.ofReal_mono
    rw [integral_const_mul, actualTargetGaussianMeasure_coordinate_second_moment,
      ← mul_assoc, target_source_weight_identity]
    exact mul_le_mul_of_nonneg_left
      (actualRawAtomicLift_integral_norm_sq_le N a mass L ha hmass hvol hL k)
      (energyWeight_nonneg k)
  have hs : Summable (fun k : Index => energyWeight k * C) := by
    have hw : Summable energyWeight := Pphi2Clean.DimensionFreeProbe.energy_weight_summable
    exact hw.mul_right C
  change (∫⁻ x, ∑' k : Index, ENNReal.ofReal ((1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2) ∂μ) ≤ _
  have hf (k : Index) : AEMeasurable
      (fun x : TargetCompletion => ENNReal.ofReal ((1 + ‖k‖) ^ 2 * ‖x k‖ ^ 2)) μ := by
    exact (ENNReal.measurable_ofReal.comp (continuous_const.mul
      (((lp.evalCLM ℂ (fun _ : Index => ℂ) 2 k).continuous.norm).pow 2)).measurable).aemeasurable
  rw [lintegral_tsum hf]
  calc
    _ ≤ ∑' k : Index, ENNReal.ofReal (energyWeight k * C) := ENNReal.tsum_le_tsum hm
    _ = ENNReal.ofReal (∑' k : Index, energyWeight k * C) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (energyWeight_nonneg k) hC) hs).symm
    _ = _ := by rw [tsum_mul_right]; congr 1; dsimp [C]; ring

theorem actualTargetProbabilityMeasure_fixedVolume_tight
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set TargetCompletion, IsCompact K ∧
      ∀ n : ℕ, (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass n :
        Measure TargetCompletion) Kᶜ ≤ ENNReal.ofReal ε := by
  let C := 2 * (mass⁻¹ ^ 2 * L ^ 122409) * ∑' k : Index, energyWeight k
  have hC : 0 ≤ C := by
    apply mul_nonneg
    · positivity
    · exact tsum_nonneg energyWeight_nonneg
  intro ε hε
  let T := C / ε + 1
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨targetEnergyBall T, isCompact_targetEnergyBall T hT.le, ?_⟩
  intro n
  let μ : Measure TargetCompletion := actualTargetProbabilityMeasure_fixedVolume L mass hL hmass n
  have hmoment : (∫⁻ x, targetSourceEnergy x ∂μ) ≤ ENNReal.ofReal C := by
    apply actualTargetGaussianMeasure_sourceEnergy_bound
    exact div_mul_cancel₀ L (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos n)))
  have hsub : (targetEnergyBall T)ᶜ ⊆ {x | ENNReal.ofReal T ≤ targetSourceEnergy x} := by
    intro x hx
    exact le_of_lt (lt_of_not_ge (fun he => hx (targetSourceEnergy_le_mem x T hT.le he)))
  have hmark := meas_ge_le_lintegral_div (μ := μ) measurable_targetSourceEnergy.aemeasurable
    (ε := ENNReal.ofReal T) (ne_of_gt (ENNReal.ofReal_pos.mpr hT)) ENNReal.ofReal_ne_top
  have hratio : C / T < ε := by
    rw [div_lt_iff₀ hT]
    have hc : ε * (C / ε) = C := by field_simp
    dsimp [T]
    nlinarith
  calc
    μ (targetEnergyBall T)ᶜ ≤ μ {x | ENNReal.ofReal T ≤ targetSourceEnergy x} := measure_mono hsub
    _ ≤ (∫⁻ x, targetSourceEnergy x ∂μ) / ENNReal.ofReal T := hmark
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal T := ENNReal.div_le_div_right hmoment _
    _ = ENNReal.ofReal (C / T) := (ENNReal.ofReal_div_of_pos hT).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_mono hratio.le

instance targetCompletion_separableSpace : TopologicalSpace.SeparableSpace TargetCompletion := by
  classical
  let S : Set TargetCompletion := ⋃ s : Finset Index, Set.range (targetHeadMap s)
  have hs : TopologicalSpace.IsSeparable S := by
    apply TopologicalSpace.IsSeparable.iUnion
    intro s
    exact TopologicalSpace.isSeparable_range (continuous_targetHeadMap s)
  obtain ⟨c, hc, hSc⟩ := hs
  have hd (x : TargetCompletion) : x ∈ closure S := by
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x)
    apply Filter.Eventually.of_forall
    intro s
    apply Set.mem_iUnion.mpr
    refine ⟨s, ?_⟩
    exact ⟨(fun k : s => x k), targetHeadMap_restrict s x⟩
  refine ⟨c, hc, ?_⟩
  intro x
  exact (isClosed_closure.closure_subset_iff.mpr hSc) (hd x)

theorem actualTargetProbabilityMeasure_fixedVolume_isTightMeasureSet
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    IsTightMeasureSet {ρ : Measure TargetCompletion | ∃ n : ℕ,
      ρ = (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass n : Measure _)} := by
  apply (isTightMeasureSet_iff_exists_isCompact_measure_compl_le).2
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ρ hρ
    simp [htop]
  · obtain ⟨K, hK, hb⟩ := actualTargetProbabilityMeasure_fixedVolume_tight L mass hL hmass
      ε.toReal (ENNReal.toReal_pos hε.ne' htop)
    refine ⟨K, hK, ?_⟩
    rintro ρ ⟨n, rfl⟩
    rw [← ENNReal.ofReal_toReal htop]
    exact hb n

theorem actualTargetProbabilityMeasure_fixedVolume_prokhorov_subsequence
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (ns : ℕ → ℕ) :
    ∃ (ms : ℕ → ℕ) (ν : ProbabilityMeasure TargetCompletion), StrictMono ms ∧
      Tendsto (fun k => actualTargetProbabilityMeasure_fixedVolume L mass hL hmass (ns (ms k)))
        atTop (𝓝 ν) := by
  let μ := actualTargetProbabilityMeasure_fixedVolume L mass hL hmass
  let S : Set (ProbabilityMeasure TargetCompletion) := Set.range μ
  have ht := actualTargetProbabilityMeasure_fixedVolume_isTightMeasureSet L mass hL hmass
  have hc : IsCompact (closure S) := by
    apply isCompact_closure_of_isTightMeasureSet
    simpa [S, Set.ext_iff, eq_comm, μ] using ht
  have hm : ∀ n, μ (ns n) ∈ closure S := fun n => subset_closure ⟨ns n, rfl⟩
  obtain ⟨ν, hν, ms, hms, hlim⟩ := hc.tendsto_subseq hm
  exact ⟨ms, ν, hms, by simpa [Function.comp_def, μ] using hlim⟩

#print axioms actualTargetProbabilityMeasure_fixedVolume_prokhorov_subsequence
#print axioms actualTargetProbabilityMeasure_fixedVolume_tight
#print axioms isCompact_targetEnergyBall

#print axioms target_isCompact_of_uniform_truncation

#print axioms targetFrequency_tail_norm_sq
#print axioms actualTargetGaussianMeasure_integral_truncation_error
end Pphi2Clean.Dim122409Gaussian
