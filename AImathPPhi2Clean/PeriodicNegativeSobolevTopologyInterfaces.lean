import AImathPPhi2Clean.PeriodicNegativeSobolevWeightComparison
import AImathPPhi2Clean.PeriodicHMinusThreeCompletion
import Mathlib.Topology.Compactness.Compact
noncomputable section
namespace Pphi2Clean.Continuum
open scoped BigOperators
def periodicHMinusTwoNorm (c : (Fin 2 → ℤ) → ℂ) : ℝ :=
  Real.sqrt (∑' k, periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2)
def periodicHMinusThreeNorm (c : (Fin 2 → ℤ) → ℂ) : ℝ :=
  Real.sqrt (∑' k, periodicHMinusThreeWeight k * ‖c k‖ ^ 2)

/-- The square of the concrete H^-2 norm is exactly the full weighted Fourier trace.
The zero mode is included because `periodicHMinusTwoFullWeight 0 = 1`. -/
theorem periodicHMinusTwoNorm_sq_eq_fullTrace
    (c : (Fin 2 → ℤ) → ℂ) (hc : c ∈ periodicHMinusTwoCarrier) :
    periodicHMinusTwoNorm c ^ 2 =
      ∑' k, periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2 := by
  unfold periodicHMinusTwoNorm
  rw [Real.sq_sqrt]
  exact tsum_nonneg (fun k => mul_nonneg
    (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _))
def PeriodicHMinusTwoNormedMeasurableCarrierInput : Prop :=
  (∀ c ∈ periodicHMinusTwoCarrier, 0 ≤ periodicHMinusTwoNorm c) ∧
  (∀ c ∈ periodicHMinusThreeCarrier, 0 ≤ periodicHMinusThreeNorm c)
def PeriodicHMinusTwoToHMinusThreeWeightRatioInput : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : Finset (Fin 2 → ℤ),
    ∀ k, k ∉ K →
      periodicHMinusThreeWeight k ≤ δ * periodicHMinusTwoFullWeight k

theorem periodicHMinusThree_weight_ratio_tendsto_zero :
    PeriodicHMinusTwoToHMinusThreeWeightRatioInput := by
  intro δ hδ
  let M : ℝ := max 1 (δ⁻¹ + 1)
  have hMone : 1 ≤ M := le_max_left _ _
  have hMdelta : δ⁻¹ < M := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  let box : Set (Fin 2 → ℤ) :=
    {k | ∀ i, k i ∈ Set.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)}
  have hbox : box.Finite := by
    apply Set.Finite.pi'
    intro i
    exact Set.finite_Icc _ _
  let K := hbox.toFinset
  refine ⟨K, ?_⟩
  intro k hk
  have hnorm : M < ‖k‖ := by
    by_contra h
    have hle : ‖k‖ ≤ M := le_of_not_gt h
    have hcoord_nat : ∀ i, (k i).natAbs ≤ ⌈M⌉₊ := by
      rw [EisensteinSeries.norm_eq_max_natAbs] at hle
      have hmax : max (k 0).natAbs (k 1).natAbs ≤ ⌈M⌉₊ := by
        exact_mod_cast le_trans hle (Nat.le_ceil M)
      intro i
      fin_cases i
      · exact (max_le_iff.mp hmax).1
      · exact (max_le_iff.mp hmax).2
    have hcoord : k ∈ box := by
      intro i
      have habs : |k i| ≤ (⌈M⌉₊ : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hcoord_nat i
      exact (abs_le.mp habs)
    have hmem : k ∈ K := hbox.mem_toFinset.mpr hcoord
    exact hk hmem
  have hk0 : k ≠ 0 := by
    intro hkz
    subst k
    have hzero : (0 : ℝ) ≤ M := by positivity
    have hcontr : M < 0 := by simpa using hnorm
    exact (not_lt_of_ge hzero) hcontr
  have hx : 0 < ‖k‖ := lt_trans (by linarith : 0 < M) hnorm
  have hxdelta : δ⁻¹ < ‖k‖ := lt_trans hMdelta hnorm
  have hsmall : ‖k‖ ^ (-2 : ℝ) ≤ δ := by
    have hmul : 1 < ‖k‖ * δ := (inv_lt_iff_one_lt_mul₀ hδ).mp hxdelta
    have hinv : ‖k‖⁻¹ ≤ δ := by
      rw [inv_le_iff_one_le_mul₀' hx]
      exact hmul.le
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)).trans
      (by rw [Real.rpow_neg_one]; exact hinv)
  have hpow : ‖k‖ ^ (-6 : ℝ) =
      ‖k‖ ^ (-4 : ℝ) * ‖k‖ ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  simp only [periodicHMinusThreeWeight, periodicHMinusTwoFullWeight,
    periodicHMinusTwoWeight, if_neg hk0]
  rw [hpow]
  calc
    ‖k‖ ^ (-4 : ℝ) * ‖k‖ ^ (-2 : ℝ) ≤
        ‖k‖ ^ (-4 : ℝ) * δ :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hx.le _)
    _ = δ * ‖k‖ ^ (-4 : ℝ) := by ring

def PeriodicHMinusTwoToHMinusThreeCompactTailInput : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
    ∃ K : Finset (Fin 2 → ℤ),
      ∀ c : (Fin 2 → ℤ) → ℂ, c ∈ periodicHMinusTwoCarrier →
        periodicHMinusTwoNorm c ≤ R →
        Real.sqrt (∑' k, if k ∉ K then
          periodicHMinusThreeWeight k * ‖c k‖ ^ 2 else 0) < ε

/-- A pointwise high-frequency comparison of the H⁻³ and H⁻² weights gives a
square-tail estimate. This is the analytic core needed before any compactness
or Borel-space argument; those remain separate inputs. -/
theorem periodicHMinusThree_tail_sq_le_of_weight_ratio
    {c : (Fin 2 → ℤ) → ℂ} (K : Finset (Fin 2 → ℤ)) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hweight : ∀ k, k ∉ K →
      periodicHMinusThreeWeight k ≤ δ * periodicHMinusTwoFullWeight k)
    (hc : c ∈ periodicHMinusTwoCarrier) :
    (∑' k, if k ∉ K then
      periodicHMinusThreeWeight k * ‖c k‖ ^ 2 else 0) ≤
      δ * (∑' k, periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) := by
  rw [periodicHMinusTwoCarrier] at hc
  have hmajor : Summable (fun k : Fin 2 → ℤ =>
      δ * (periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2)) := by
    simpa only [mul_assoc] using (hc.mul_left δ)
  have htail : Summable (fun k : Fin 2 → ℤ => if k ∉ K then
      periodicHMinusThreeWeight k * ‖c k‖ ^ 2 else 0) := by
    refine Summable.of_nonneg_of_le
      (f := fun k : Fin 2 → ℤ => δ *
        (periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2))
      (g := fun k : Fin 2 → ℤ => if k ∉ K then
        periodicHMinusThreeWeight k * ‖c k‖ ^ 2 else 0) ?_ ?_ hmajor
    · intro k
      by_cases hk : k ∈ K
      · simp [hk]
      · simp [hk]
        exact mul_nonneg (periodicHMinusThreeWeight_nonneg k) (sq_nonneg _)
    · intro k
      by_cases hk : k ∈ K
      · simp [hk]
        exact mul_nonneg hδ (mul_nonneg
          (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _))
      · simp [hk]
        simpa [hk, mul_assoc] using
          (mul_le_mul_of_nonneg_right (hweight k hk) (sq_nonneg (‖c k‖)))
  calc
    (∑' k, if k ∉ K then
      periodicHMinusThreeWeight k * ‖c k‖ ^ 2 else 0) ≤
        ∑' k, δ * (periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) := by
      exact htail.tsum_le_tsum (fun k => by
        by_cases hk : k ∈ K
        · simp [hk]
          exact mul_nonneg hδ (mul_nonneg
            (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _))
        · simp [hk]
          simpa [hk, mul_assoc] using
            (mul_le_mul_of_nonneg_right (hweight k hk) (sq_nonneg (‖c k‖)))) hmajor
    _ = δ * (∑' k, periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) := by
      rw [tsum_mul_left]

theorem periodicHMinusThree_compact_tail_of_weight_ratio
    (hweightRatio : PeriodicHMinusTwoToHMinusThreeWeightRatioInput) :
    PeriodicHMinusTwoToHMinusThreeCompactTailInput := by
  intro R hR ε hε
  let δ := (ε / (R + 1)) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδle : 0 ≤ δ := hδ.le
  obtain ⟨K, hK⟩ := hweightRatio δ hδ
  refine ⟨K, ?_⟩
  intro c hc hnorm
  have hsum : Summable (fun k : Fin 2 → ℤ =>
      periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) := by
    simpa [periodicHMinusTwoCarrier] using hc
  have hnorm_sq :
      (∑' k : Fin 2 → ℤ,
        periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) ≤ R ^ 2 := by
    change Real.sqrt (∑' k : Fin 2 → ℤ,
      periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) ≤ R at hnorm
    exact (Real.sqrt_le_iff).mp hnorm |>.2
  have htail := periodicHMinusThree_tail_sq_le_of_weight_ratio K δ hδle hK hc
  have htail_nonneg : 0 ≤ ∑' k : Fin 2 → ℤ, if k ∉ K then
      periodicHMinusThreeWeight k * ‖c k‖ ^ 2 else 0 :=
    tsum_nonneg fun k => by
      by_cases hk : k ∉ K
      · simp [hk]
        exact mul_nonneg (periodicHMinusThreeWeight_nonneg k) (sq_nonneg ‖c k‖)
      · simp [hk]
  apply (Real.sqrt_lt htail_nonneg hε.le).2
  calc
    (∑' k : Fin 2 → ℤ, if k ∉ K then
        periodicHMinusThreeWeight k * ‖c k‖ ^ 2 else 0) ≤
        δ * (∑' k : Fin 2 → ℤ,
          periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) := htail
    _ ≤ δ * R ^ 2 := mul_le_mul_of_nonneg_left hnorm_sq hδle
    _ < ε ^ 2 := by
      dsimp [δ]
      have hden : 0 < R + 1 := by linarith
      have hratio_nonneg : 0 ≤ R / (R + 1) := div_nonneg hR hden.le
      have hratio_lt : R / (R + 1) < 1 := (div_lt_one hden).2 (by linarith)
      have hratio_sq : (R / (R + 1)) ^ 2 < 1 := by
        have hsum_pos : 0 < 1 + R / (R + 1) := by linarith
        nlinarith [mul_pos (sub_pos.mpr hratio_lt) hsum_pos]
      have hcalc :
          (ε / (R + 1)) ^ 2 * R ^ 2 =
            ε ^ 2 * (R / (R + 1)) ^ 2 := by
        field_simp [ne_of_gt hden] <;> ring
      rw [hcalc]
      calc
        ε ^ 2 * (R / (R + 1)) ^ 2 < ε ^ 2 * 1 :=
          mul_lt_mul_of_pos_left hratio_sq (sq_pos_of_pos hε)
        _ = ε ^ 2 := by ring

theorem weightedCoefficients_memLp2_of_hminus2
    (c : (Fin 2 → ℤ) → ℂ) (hc : c ∈ periodicHMinusTwoCarrier) :
    Memℓp (periodicHMinusThreeWeightedCoefficients c) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  change Summable (fun k =>
    ‖(Real.sqrt (periodicHMinusThreeWeight k) : ℂ) * c k‖ ^ (2 : ℝ))
  rw [periodicHMinusTwoCarrier] at hc
  apply Summable.of_nonneg_of_le
    (fun k => by positivity)
    (fun k => ?_) hc
  have hw := periodicHMinusThreeWeight_nonneg k
  calc
    ‖(Real.sqrt (periodicHMinusThreeWeight k) : ℂ) * c k‖ ^ (2 : ℝ) =
        periodicHMinusThreeWeight k * ‖c k‖ ^ 2 := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Real.sq_sqrt hw]
    _ ≤ periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (periodicHMinusThreeWeight_le_periodicHMinusTwoFullWeight k)
        (sq_nonneg ‖c k‖)

def periodicHMinusThreeEmbeddingOfHMinusTwo
    (c : (Fin 2 → ℤ) → ℂ) (hc : c ∈ periodicHMinusTwoCarrier) :
    PeriodicHMinusThreeCompletion :=
  ⟨periodicHMinusThreeWeightedCoefficients c,
    weightedCoefficients_memLp2_of_hminus2 c hc⟩

theorem periodicHMinusThreeNorm_le_periodicHMinusTwoNorm
    (c : (Fin 2 → ℤ) → ℂ) (hc : c ∈ periodicHMinusTwoCarrier) :
    periodicHMinusThreeNorm c ≤ periodicHMinusTwoNorm c := by
  rw [periodicHMinusTwoCarrier] at hc
  have h3sum : Summable (fun k : Fin 2 → ℤ =>
      periodicHMinusThreeWeight k * ‖c k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (periodicHMinusThreeWeight_nonneg k) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right
        (periodicHMinusThreeWeight_le_periodicHMinusTwoFullWeight k)
        (sq_nonneg ‖c k‖)) hc
  unfold periodicHMinusThreeNorm periodicHMinusTwoNorm
  apply Real.sqrt_le_sqrt
  exact h3sum.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right
      (periodicHMinusThreeWeight_le_periodicHMinusTwoFullWeight k)
      (sq_nonneg ‖c k‖)) hc

    (z : {k // k ∈ K} → ℂ) : PeriodicHMinusThreeCompletion :=
  ∑ k : {k // k ∈ K}, lp.single (E := fun _ : Fin 2 → ℤ => ℂ)
    2 (k : Fin 2 → ℤ) (z k)

theorem continuous_periodicHMinusThreeFiniteFourierProjection
    (K : Finset (Fin 2 → ℤ)) :
    Continuous (periodicHMinusThreeFiniteFourierProjection K) := by
  apply continuous_finsetSum
  intro k hk
  exact (lp.singleContinuousAddMonoidHom
    (fun _ : Fin 2 → ℤ => ℂ) 2 (k : Fin 2 → ℤ)).continuous.comp
      (continuous_apply k)

theorem periodicHMinusThreeFiniteFourierProjection_boundedBall_compact
    (K : Finset (Fin 2 → ℤ)) (B : ℝ) :
    IsCompact (periodicHMinusThreeFiniteFourierProjection K ''
      {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B}) := by
  have hpi : IsCompact {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B} := by
    convert (isCompact_pi_infinite (fun _ : {k // k ∈ K} =>
      isCompact_closedBall (0 : ℂ) B)) using 1
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  exact hpi.image (continuous_periodicHMinusThreeFiniteFourierProjection K)

/-- Any set uniformly approximable, at every positive accuracy, by compact sets is
totally bounded. The accuracy remains universally quantified. -/
theorem totallyBounded_of_compact_approximation
    {E : Type*} [PseudoMetricSpace E] {S : Set E}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ T : Set E,
      IsCompact T ∧ ∀ x ∈ S, ∃ y ∈ T, dist x y < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨T, hT, happroxT⟩ := happrox (ε / 2) (by positivity)
  obtain ⟨centers, hfinite, hcover⟩ :=
    (Metric.totallyBounded_iff.mp hT.totallyBounded) (ε / 2) (by positivity)
  refine ⟨centers, hfinite, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := happroxT x hx
  have hycover : y ∈ ⋃ z ∈ centers, Metric.ball z (ε / 2) := hcover hy
  rcases Set.mem_iUnion.mp hycover with ⟨z, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hzc, hyball⟩
  refine Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzc, ?_⟩⟩
  apply Metric.mem_ball.mpr
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy (Metric.mem_ball.mp hyball)
    _ = ε := by ring

/-- In a complete metric space, the closure of a totally bounded set is compact. -/
theorem isCompact_closure_of_totallyBounded
    {E : Type*} [PseudoMetricSpace E] [CompleteSpace E] {S : Set E}
    (hS : TotallyBounded S) : IsCompact (closure S) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨hS.closure, isClosed_closure.isComplete⟩

theorem periodicHMinusThreeEmbedding_norm_eq
    (c : (Fin 2 → ℤ) → ℂ) (hc : c ∈ periodicHMinusTwoCarrier) :
    ‖periodicHMinusThreeEmbeddingOfHMinusTwo c hc‖ = periodicHMinusThreeNorm c := by
  unfold periodicHMinusThreeNorm
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply tsum_congr
  intro k
  simp only [periodicHMinusThreeEmbeddingOfHMinusTwo,
    periodicHMinusThreeWeightedCoefficients]
  have hw := periodicHMinusThreeWeight_nonneg k
  have hnorm :
      ‖(Real.sqrt (periodicHMinusThreeWeight k) : ℂ) * c k‖ ^ (2 : ℝ) =
        periodicHMinusThreeWeight k * ‖c k‖ ^ 2 := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt hw]
  exact hnorm

theorem lp_fourier_projection_error_sq_eq_tail
    (K : Finset (Fin 2 → ℤ)) (x : PeriodicHMinusThreeCompletion) :
    ‖x - periodicHMinusThreeFiniteFourierProjection K
      (fun k => x (k : Fin 2 → ℤ))‖ ^ (2 : ℝ) =
      ∑' k : Fin 2 → ℤ, if k ∉ K then ‖x k‖ ^ 2 else 0 := by
  let hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hsum : Summable (fun k : Fin 2 → ℤ => ‖x k‖ ^ (2 : ℝ)) :=
    (lp.memℓp x).summable hp
  have hsplit := hsum.sum_add_tsum_compl (s := K)
  have hnormx := lp.norm_rpow_eq_tsum hp x
  have hnormdiff := lp.norm_compl_sum_single hp x K
  have htail :
      (∑' k : Fin 2 → ℤ, if k ∉ K then ‖x k‖ ^ 2 else 0) =
        ∑' j : {k : (Fin 2 → ℤ) // k ∈ (↑K : Set (Fin 2 → ℤ))ᶜ},
          ‖x j‖ ^ (2 : ℝ) := by
    calc
      (∑' k : Fin 2 → ℤ, if k ∉ K then ‖x k‖ ^ 2 else 0) =
          ∑' k : Fin 2 → ℤ,
            ((↑K : Set (Fin 2 → ℤ))ᶜ).indicator (fun k => ‖x k‖ ^ 2) k := by
        congr 1
        funext k
        by_cases hk : k ∈ K <;> simp [Set.indicator, hk]
      _ = ∑' j : {k : (Fin 2 → ℤ) // k ∈ (↑K : Set (Fin 2 → ℤ))ᶜ},
          ‖x j‖ ^ (2 : ℝ) := (tsum_subtype _ _).symm
  simp only [ENNReal.toReal_ofNat] at hnormx hnormdiff
  have hnormdiff' :
      ‖x - periodicHMinusThreeFiniteFourierProjection K
          (fun k => x (k : Fin 2 → ℤ))‖ ^ (2 : ℝ) =
        ‖x‖ ^ (2 : ℝ) - ∑ k ∈ K, ‖x k‖ ^ (2 : ℝ) := by
    simpa [periodicHMinusThreeFiniteFourierProjection] using hnormdiff
  calc
    ‖x - periodicHMinusThreeFiniteFourierProjection K
        (fun k => x (k : Fin 2 → ℤ))‖ ^ (2 : ℝ) =
        ‖x‖ ^ (2 : ℝ) - ∑ k ∈ K, ‖x k‖ ^ (2 : ℝ) := hnormdiff'
    _ = ∑' j : {k : (Fin 2 → ℤ) // k ∈ (↑K : Set (Fin 2 → ℤ))ᶜ},
          ‖x j‖ ^ (2 : ℝ) := by
      rw [hnormx]
      linarith [hsplit]
    _ = ∑' k : Fin 2 → ℤ, if k ∉ K then ‖x k‖ ^ 2 else 0 := htail.symm

def periodicHMinusTwoBallInHMinusThree (B : ℝ) : Set PeriodicHMinusThreeCompletion :=
  {x | ∃ c : (Fin 2 → ℤ) → ℂ, ∃ hc : c ∈ periodicHMinusTwoCarrier,
    periodicHMinusTwoNorm c ≤ B ∧
    x = periodicHMinusThreeEmbeddingOfHMinusTwo c hc}

theorem periodicHMinusTwoBall_compact_approximation (B : ℝ) (hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Set PeriodicHMinusThreeCompletion, IsCompact T ∧
      ∀ x ∈ periodicHMinusTwoBallInHMinusThree B, ∃ y ∈ T, dist x y < ε := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ := periodicHMinusThree_compact_tail_of_weight_ratio
    periodicHMinusThree_weight_ratio_tendsto_zero B hB η hη
  let T := periodicHMinusThreeFiniteFourierProjection K ''
    {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B}
  have hT : IsCompact T :=
    periodicHMinusThreeFiniteFourierProjection_boundedBall_compact K B
  refine ⟨T, hT, ?_⟩
  intro x hx
  rcases hx with ⟨c, hc, hcB, rfl⟩
  let xh := periodicHMinusThreeEmbeddingOfHMinusTwo c hc
  let z : {k // k ∈ K} → ℂ := fun k => xh (k : Fin 2 → ℤ)
  have hz : ∀ k, ‖z k‖ ≤ B := by
    intro k
    calc
      ‖z k‖ ≤ ‖xh‖ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) xh _
      _ = periodicHMinusThreeNorm c := periodicHMinusThreeEmbedding_norm_eq c hc
      _ ≤ periodicHMinusTwoNorm c := periodicHMinusThreeNorm_le_periodicHMinusTwoNorm c hc
      _ ≤ B := hcB
  let y := periodicHMinusThreeFiniteFourierProjection K z
  refine ⟨y, ⟨z, hz, rfl⟩, ?_⟩
  have htail := hK c hc hcB
  let q : ℝ := ∑' k : Fin 2 → ℤ, if k ∉ K then
    periodicHMinusThreeWeight k * ‖c k‖ ^ 2 else 0
  have hq : 0 ≤ q := by
    dsimp [q]
    apply tsum_nonneg
    intro k
    by_cases hk : k ∉ K
    · simp [hk]
      exact mul_nonneg (periodicHMinusThreeWeight_nonneg k) (sq_nonneg ‖c k‖)
    · simp [hk]
  have hqη : Real.sqrt q < η := by
    dsimp [q] at htail ⊢
    exact htail
  have herror_sq : ‖xh - y‖ ^ (2 : ℝ) = q := by
    rw [lp_fourier_projection_error_sq_eq_tail]
    dsimp [y, z, xh, q]
    apply tsum_congr
    intro k
    by_cases hk : k ∉ K
    · simp only [hk]
      change ‖periodicHMinusThreeWeightedCoefficients c k‖ ^ 2 =
        periodicHMinusThreeWeight k * ‖c k‖ ^ 2
      have hw := periodicHMinusThreeWeight_nonneg k
      simp [periodicHMinusThreeWeightedCoefficients, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Real.sq_sqrt hw]
    · simp [hk]
  have hnorm_eq : ‖xh - y‖ = Real.sqrt q := by
    calc
      ‖xh - y‖ = Real.sqrt (‖xh - y‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt q := by
        congr 1
        exact_mod_cast herror_sq
  dsimp [η] at hqη
  calc
    dist xh y = ‖xh - y‖ := dist_eq_norm xh y
    _ = Real.sqrt q := hnorm_eq
    _ < ε / 2 := hqη
    _ < ε := by linarith

theorem periodicHMinusTwoBallInHMinusThree_totallyBounded
    (B : ℝ) (hB : 0 ≤ B) :
    TotallyBounded (periodicHMinusTwoBallInHMinusThree B) :=
  totallyBounded_of_compact_approximation
    (periodicHMinusTwoBall_compact_approximation B hB)

theorem isCompact_closure_periodicHMinusTwoBallInHMinusThree
    (B : ℝ) (hB : 0 ≤ B) :
    IsCompact (closure (periodicHMinusTwoBallInHMinusThree B)) :=
  isCompact_closure_of_totallyBounded
    (periodicHMinusTwoBallInHMinusThree_totallyBounded B hB)


