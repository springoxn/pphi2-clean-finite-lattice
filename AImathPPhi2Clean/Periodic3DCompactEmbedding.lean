import AImathPPhi2Clean.Periodic3DWeightedCarrier

noncomputable section
namespace Pphi2Clean.Continuum

abbrev Periodic3DHminusFourCompletion := Periodic3DCompletion
abbrev periodic3DHminusThreeCoefficientCarrier := periodic3DCarrier 3
abbrev periodic3DHminusFourCoefficientCarrier := periodic3DCarrier 4
abbrev periodic3DHminusFourEmbeddingOfCoefficients := periodic3DEmbeddingOfCoefficients 4

theorem periodic3D_hminus3_coefficients_in_hminus4 (c : Periodic3DIndex → ℂ)
    (hc : c ∈ periodic3DHminusThreeCoefficientCarrier) :
    c ∈ periodic3DHminusFourCoefficientCarrier := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (periodic3DHminusFourWeight_nonneg k) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right (periodic3DHminusFourWeight_le_three k) (sq_nonneg _)) hc

theorem periodic3D_weight_ratio_tendsto_zero :
    ∀ δ : ℝ, 0 < δ → ∃ K : Finset Periodic3DIndex,
      ∀ k, k ∉ K → periodic3DSobolevWeight 4 k ≤ δ * periodic3DSobolevWeight 3 k := by
  intro δ hδ
  obtain ⟨K, hK⟩ := fs4_weight_ratio_tendsto_zero δ hδ
  refine ⟨K.preimage periodic3DExtend periodic3DExtend_injective.injOn, ?_⟩
  intro k hk
  exact hK (periodic3DExtend k) (by simpa only [Finset.mem_preimage] using hk)

theorem periodic3D_hminus4_tail_sq_le_of_weight_ratio
    {c : Periodic3DIndex → ℂ} (K : Finset Periodic3DIndex) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hweight : ∀ k, k ∉ K → periodic3DSobolevWeight 4 k ≤ δ * periodic3DSobolevWeight 3 k)
    (hc : Summable (fun k : Periodic3DIndex => periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2)) :
    (∑' k, if k ∉ K then periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 else 0) ≤
      δ * (∑' k, periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2) := by
  have hmajor : Summable (fun k : Periodic3DIndex =>
      δ * (periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2)) := by
    simpa only [mul_assoc] using hc.mul_left δ
  have htail : Summable (fun k : Periodic3DIndex => if k ∉ K then
      periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 else 0) := by
    refine Summable.of_nonneg_of_le
      (f := fun k : Periodic3DIndex => δ * (periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2))
      (g := fun k : Periodic3DIndex => if k ∉ K then
        periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 else 0) ?_ ?_ hmajor
    · intro k
      by_cases hk : k ∈ K
      · simp [hk]
      · simp [hk]
        exact mul_nonneg (periodic3DSobolevWeight_nonneg 4 k) (sq_nonneg _)
    · intro k
      by_cases hk : k ∈ K
      · simp [hk]
        exact mul_nonneg hδ (mul_nonneg (periodic3DSobolevWeight_nonneg 3 k) (sq_nonneg _))
      · simp [hk]
        simpa [hk, mul_assoc] using
          (mul_le_mul_of_nonneg_right (hweight k hk) (sq_nonneg (‖c k‖)))
  calc
    (∑' k : Periodic3DIndex, if k ∉ K then
        periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 else 0) ≤
        ∑' k, δ * (periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2) := by
      exact htail.tsum_le_tsum (fun k => by
        by_cases hk : k ∈ K
        · simp [hk]
          exact mul_nonneg hδ (mul_nonneg (periodic3DSobolevWeight_nonneg 3 k) (sq_nonneg _))
        · simp [hk]
          simpa [hk, mul_assoc] using
            (mul_le_mul_of_nonneg_right (hweight k hk) (sq_nonneg (‖c k‖)))) hmajor
    _ = δ * (∑' k, periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2) := by
      rw [tsum_mul_left]

theorem periodic3D_hminus4_uniform_tail_of_hminus3_bound :
    ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
      ∃ K : Finset Periodic3DIndex, ∀ c : Periodic3DIndex → ℂ,
        Summable (fun k => periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2) →
        periodic3DHminusThreeNorm c ≤ R →
        Real.sqrt (∑' k, if k ∉ K then
          periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 else 0) < ε := by
  intro R hR ε hε
  let δ := (ε / (R + 1)) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨K, hK⟩ := periodic3D_weight_ratio_tendsto_zero δ hδ
  refine ⟨K, ?_⟩
  intro c hc hnorm
  have hnorm_sq :
      (∑' k : Periodic3DIndex, periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2) ≤ R ^ 2 := by
    change Real.sqrt (∑' k : Periodic3DIndex,
      periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2) ≤ R at hnorm
    exact (Real.sqrt_le_iff).mp hnorm |>.2
  have htail := periodic3D_hminus4_tail_sq_le_of_weight_ratio K δ hδ.le hK hc
  have htail_nonneg : 0 ≤ ∑' k : Periodic3DIndex, if k ∉ K then
      periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 else 0 :=
    tsum_nonneg fun k => by
      by_cases hk : k ∉ K
      · simp [hk]
        exact mul_nonneg (periodic3DSobolevWeight_nonneg 4 k) (sq_nonneg ‖c k‖)
      · simp [hk]
  apply (Real.sqrt_lt htail_nonneg hε.le).2
  calc
    (∑' k : Periodic3DIndex, if k ∉ K then
        periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 else 0) ≤
        δ * (∑' k : Periodic3DIndex,
          periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2) := htail
    _ ≤ δ * R ^ 2 := mul_le_mul_of_nonneg_left hnorm_sq hδ.le
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

def periodic3DHminusFourFiniteProjection (K : Finset Periodic3DIndex)
    (z : {k // k ∈ K} → ℂ) : Periodic3DHminusFourCompletion :=
  ∑ k : {k // k ∈ K}, lp.single (E := fun _ : Periodic3DIndex => ℂ)
    2 (k : Periodic3DIndex) (z k)

theorem periodic3DHminusFourFiniteProjection_continuous (K : Finset Periodic3DIndex) :
    Continuous (periodic3DHminusFourFiniteProjection K) := by
  apply continuous_finsetSum
  intro k hk
  exact (lp.singleContinuousAddMonoidHom
    (fun _ : Periodic3DIndex => ℂ) 2 (k : Periodic3DIndex)).continuous.comp
      (continuous_apply k)

theorem periodic3DHminusFourFiniteProjection_boundedBall_compact
    (K : Finset Periodic3DIndex) (B : ℝ) :
    IsCompact (periodic3DHminusFourFiniteProjection K ''
      {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B}) := by
  have hpi : IsCompact {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B} := by
    convert (isCompact_pi_infinite (fun _ : {k // k ∈ K} =>
      isCompact_closedBall (0 : ℂ) B)) using 1
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  exact hpi.image (periodic3DHminusFourFiniteProjection_continuous K)


theorem periodic3DHminusFourEmbedding_norm_eq (c : Periodic3DIndex → ℂ)
    (hc : c ∈ periodic3DHminusFourCoefficientCarrier) :
    ‖periodic3DHminusFourEmbeddingOfCoefficients c hc‖ = periodic3DHminusFourNorm c := by
  unfold periodic3DHminusFourNorm
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply tsum_congr
  intro k
  simp only [periodic3DHminusFourEmbeddingOfCoefficients, periodic3DEmbeddingOfCoefficients, periodic3DWeightedFourierCoefficients]
  have hw := periodic3DSobolevWeight_nonneg 4 k
  have hnorm :
      ‖(Real.sqrt (periodic3DSobolevWeight 4 k) : ℂ) * c k‖ ^ (2 : ℝ) =
        periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt hw]
  exact hnorm

theorem periodic3DHminusFourEmbedding_norm_le_three_compact (c : Periodic3DIndex → ℂ)
    (hc : c ∈ periodic3DHminusThreeCoefficientCarrier) :
    ‖periodic3DHminusFourEmbeddingOfCoefficients c
      (periodic3D_hminus3_coefficients_in_hminus4 c hc)‖ ≤ periodic3DHminusThreeNorm c := by
  have hc4 := periodic3D_hminus3_coefficients_in_hminus4 c hc
  have hsum4 : Summable (fun k => periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2) := hc4
  have hnn4 : ∀ k : Periodic3DIndex, 0 ≤ periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 :=
    fun k => mul_nonneg (periodic3DSobolevWeight_nonneg 4 k) (sq_nonneg _)
  have hnn3 : ∀ k : Periodic3DIndex, 0 ≤ periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 :=
    fun k => mul_nonneg (periodic3DSobolevWeight_nonneg 3 k) (sq_nonneg _)
  have hle : ∀ k : Periodic3DIndex,
      periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 ≤ periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 :=
    fun k => mul_le_mul_of_nonneg_right (periodic3DHminusFourWeight_le_three k) (sq_nonneg _)
  have hE : (∑' k : Periodic3DIndex,
      ENNReal.ofReal (periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2)) ≤
      ∑' k : Periodic3DIndex,
        ENNReal.ofReal (periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2) :=
    ENNReal.tsum_le_tsum (fun k => ENNReal.ofReal_le_ofReal (hle k))
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn4 hsum4,
      ← ENNReal.ofReal_tsum_of_nonneg hnn3 hc] at hE
  have hreal :
      (∑' k : Periodic3DIndex, periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2) ≤
        ∑' k : Periodic3DIndex, periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hnn3)).mp hE
  rw [periodic3DHminusFourEmbedding_norm_eq c hc4]
  unfold periodic3DHminusFourNorm periodic3DHminusThreeNorm
  exact Real.sqrt_le_sqrt hreal

theorem periodic3D_lp_fourier_projection_error_sq_eq_tail
    (K : Finset Periodic3DIndex) (x : Periodic3DHminusFourCompletion) :
    ‖x - periodic3DHminusFourFiniteProjection K (fun k => x (k : Periodic3DIndex))‖ ^ (2 : ℝ) =
      ∑' k : Periodic3DIndex, if k ∉ K then ‖x k‖ ^ 2 else 0 := by
  let hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hsum : Summable (fun k : Periodic3DIndex => ‖x k‖ ^ (2 : ℝ)) :=
    (lp.memℓp x).summable hp
  have hsplit := hsum.sum_add_tsum_compl (s := K)
  have hnormx := lp.norm_rpow_eq_tsum hp x
  have hnormdiff := lp.norm_compl_sum_single hp x K
  have htail :
      (∑' k : Periodic3DIndex, if k ∉ K then ‖x k‖ ^ 2 else 0) =
        ∑' j : {k : Periodic3DIndex // k ∈ (↑K : Set Periodic3DIndex)ᶜ}, ‖x j‖ ^ (2 : ℝ) := by
    calc
      (∑' k : Periodic3DIndex, if k ∉ K then ‖x k‖ ^ 2 else 0) =
          ∑' k : Periodic3DIndex, ((↑K : Set Periodic3DIndex)ᶜ).indicator
            (fun k => ‖x k‖ ^ 2) k := by
        congr 1
        funext k
        by_cases hk : k ∈ K <;> simp [Set.indicator, hk]
      _ = ∑' j : {k : Periodic3DIndex // k ∈ (↑K : Set Periodic3DIndex)ᶜ},
            ‖x j‖ ^ (2 : ℝ) := (tsum_subtype _ _).symm
  simp only [ENNReal.toReal_ofNat] at hnormx hnormdiff
  have hnormdiff' :
      ‖x - periodic3DHminusFourFiniteProjection K (fun k => x (k : Periodic3DIndex))‖ ^ (2 : ℝ) =
        ‖x‖ ^ (2 : ℝ) - ∑ k ∈ K, ‖x k‖ ^ (2 : ℝ) := by
    simpa [periodic3DHminusFourFiniteProjection] using hnormdiff
  calc
    ‖x - periodic3DHminusFourFiniteProjection K (fun k => x (k : Periodic3DIndex))‖ ^ (2 : ℝ) =
        ‖x‖ ^ (2 : ℝ) - ∑ k ∈ K, ‖x k‖ ^ (2 : ℝ) := hnormdiff'
    _ = ∑' j : {k : Periodic3DIndex // k ∈ (↑K : Set Periodic3DIndex)ᶜ},
          ‖x j‖ ^ (2 : ℝ) := by
      rw [hnormx]
      linarith [hsplit]
    _ = ∑' k : Periodic3DIndex, if k ∉ K then ‖x k‖ ^ 2 else 0 := htail.symm

def periodic3DHminusThreeBallInHminusFour (B : ℝ) : Set Periodic3DHminusFourCompletion :=
  {x | ∃ c : Periodic3DIndex → ℂ, ∃ hc : c ∈ periodic3DHminusThreeCoefficientCarrier,
    periodic3DHminusThreeNorm c ≤ B ∧
      x = periodic3DHminusFourEmbeddingOfCoefficients c
        (periodic3D_hminus3_coefficients_in_hminus4 c hc)}

theorem periodic3DHminusThreeBall_compact_approximation (B : ℝ) (hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Set Periodic3DHminusFourCompletion, IsCompact T ∧
      ∀ x ∈ periodic3DHminusThreeBallInHminusFour B, ∃ y ∈ T, dist x y < ε := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ := periodic3D_hminus4_uniform_tail_of_hminus3_bound B hB η hη
  let T := periodic3DHminusFourFiniteProjection K ''
    {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B}
  have hT : IsCompact T := periodic3DHminusFourFiniteProjection_boundedBall_compact K B
  refine ⟨T, hT, ?_⟩
  intro x hx
  rcases hx with ⟨c, hc, hcB, rfl⟩
  let h4 := periodic3D_hminus3_coefficients_in_hminus4 c hc
  let xh := periodic3DHminusFourEmbeddingOfCoefficients c h4
  let z : {k // k ∈ K} → ℂ := fun k => xh (k : Periodic3DIndex)
  have hz : ∀ k, ‖z k‖ ≤ B := by
    intro k
    calc
      ‖z k‖ ≤ ‖xh‖ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) xh _
      _ = periodic3DHminusFourNorm c := periodic3DHminusFourEmbedding_norm_eq c h4
      _ ≤ periodic3DHminusThreeNorm c := by
        calc
          periodic3DHminusFourNorm c = ‖periodic3DHminusFourEmbeddingOfCoefficients c h4‖ :=
            (periodic3DHminusFourEmbedding_norm_eq c h4).symm
          _ ≤ periodic3DHminusThreeNorm c := periodic3DHminusFourEmbedding_norm_le_three_compact c hc
      _ ≤ B := hcB
  let y := periodic3DHminusFourFiniteProjection K z
  refine ⟨y, ⟨z, hz, rfl⟩, ?_⟩
  have htail := hK c hc hcB
  let q : ℝ := ∑' k : Periodic3DIndex, if k ∉ K then
    periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2 else 0
  have hq : 0 ≤ q := by
    dsimp [q]
    apply tsum_nonneg
    intro k
    by_cases hk : k ∉ K
    · simp [hk]
      exact mul_nonneg (periodic3DSobolevWeight_nonneg 4 k) (sq_nonneg _)
    · simp [hk]
  have hqη : Real.sqrt q < η := by
    dsimp [q] at htail ⊢
    exact htail
  have herror_sq : ‖xh - y‖ ^ (2 : ℝ) = q := by
    rw [periodic3D_lp_fourier_projection_error_sq_eq_tail]
    dsimp [y, z, xh, q]
    apply tsum_congr
    intro k
    by_cases hk : k ∉ K
    · simp only [hk]
      change ‖periodic3DWeightedFourierCoefficients 4 c k‖ ^ 2 =
        periodic3DSobolevWeight 4 k * ‖c k‖ ^ 2
      have hw := periodic3DSobolevWeight_nonneg 4 k
      simp [periodic3DWeightedFourierCoefficients, Complex.norm_real,
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

theorem periodic3D_totallyBounded_of_compact_approximation
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

theorem periodic3DHminusThreeBall_totallyBounded (B : ℝ) (hB : 0 ≤ B) :
    TotallyBounded (periodic3DHminusThreeBallInHminusFour B) :=
  periodic3D_totallyBounded_of_compact_approximation
    (periodic3DHminusThreeBall_compact_approximation B hB)

theorem isCompact_closure_periodic3DHminusThreeBall (B : ℝ) (hB : 0 ≤ B) :
    IsCompact (closure (periodic3DHminusThreeBallInHminusFour B)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨(periodic3DHminusThreeBall_totallyBounded B hB).closure,
    isClosed_closure.isComplete⟩

theorem periodic3DHminusFour_finite_truncations_approx
    (x : Periodic3DHminusFourCompletion) {eps : ℝ} (heps : 0 < eps) :
    ∃ s : Finset Periodic3DIndex,
      ‖x - ∑ i ∈ s, lp.single (E := fun _ : Periodic3DIndex => ℂ) 2 i (x i)‖ < eps := by
  have hs : HasSum (fun i : Periodic3DIndex =>
      lp.single (E := fun _ : Periodic3DIndex => ℂ) 2 i (x i)) x :=
    lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
  rw [HasSum, Metric.tendsto_nhds] at hs
  rcases Filter.eventually_atTop.1 (hs eps heps) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  have hdist := hs s (le_rfl)
  simpa [dist_eq_norm, norm_sub_rev] using hdist

def periodic3DHminusFourFiniteSupportSum
    (v : Σ s : Finset Periodic3DIndex, ({i // i ∈ s} → ℂ)) : Periodic3DHminusFourCompletion :=
  periodic3DHminusFourFiniteProjection v.1 v.2

theorem periodic3DHminusFourFiniteSupportSum_continuous :
    Continuous periodic3DHminusFourFiniteSupportSum := by
  apply continuous_sigma
  intro s
  exact periodic3DHminusFourFiniteProjection_continuous s

theorem periodic3DHminusFourFiniteSupportSum_denseRange :
    DenseRange periodic3DHminusFourFiniteSupportSum := by
  rw [Metric.denseRange_iff]
  intro x eps heps
  obtain ⟨s, hs⟩ := periodic3DHminusFour_finite_truncations_approx x heps
  refine ⟨⟨s, fun i => x i⟩, ?_⟩
  simpa [dist_eq_norm, periodic3DHminusFourFiniteSupportSum,
    periodic3DHminusFourFiniteProjection] using hs

theorem periodic3DHminusFourCompletion_separable :
    TopologicalSpace.SeparableSpace Periodic3DHminusFourCompletion := by
  have hdense : Dense (Set.range periodic3DHminusFourFiniteSupportSum) :=
    periodic3DHminusFourFiniteSupportSum_denseRange
  have hsep : TopologicalSpace.IsSeparable (Set.range periodic3DHminusFourFiniteSupportSum) :=
    TopologicalSpace.isSeparable_range periodic3DHminusFourFiniteSupportSum_continuous
  exact (hdense.isSeparable_iff).mp hsep
end Pphi2Clean.Continuum
