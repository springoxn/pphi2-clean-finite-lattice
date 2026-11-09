import AImathPPhi2Clean.PeriodicFS4DWeightedCarrier

noncomputable section

namespace Pphi2Clean.Continuum

def fs4HminusFourNorm (c : FS4Index → ℂ) : ℝ :=
  Real.sqrt (∑' k, fs4SobolevWeight 4 k * ‖c k‖ ^ 2)

theorem fs4HminusFourEmbedding_norm_eq (c : FS4Index → ℂ)
    (hc : c ∈ fs4HminusFourCoefficientCarrier) :
    ‖fs4HminusFourEmbeddingOfCoefficients c hc‖ = fs4HminusFourNorm c := by
  unfold fs4HminusFourNorm
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply tsum_congr
  intro k
  simp only [fs4HminusFourEmbeddingOfCoefficients, fs4WeightedFourierCoefficients]
  have hw := fs4SobolevWeight_nonneg 4 k
  have hnorm :
      ‖(Real.sqrt (fs4SobolevWeight 4 k) : ℂ) * c k‖ ^ (2 : ℝ) =
        fs4SobolevWeight 4 k * ‖c k‖ ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt hw]
  exact hnorm

theorem fs4HminusFourEmbedding_norm_le_hminusThreeNorm (c : FS4Index → ℂ)
    (hc : c ∈ fs4HminusThreeCoefficientCarrier) :
    ‖fs4HminusFourEmbeddingOfCoefficients c
      (fs4_hminus3_coefficients_in_hminus4 c hc)‖ ≤ fs4HminusThreeNorm c := by
  have hc4 := fs4_hminus3_coefficients_in_hminus4 c hc
  have hsum4 : Summable (fun k => fs4SobolevWeight 4 k * ‖c k‖ ^ 2) := hc4
  have hnn4 : ∀ k : FS4Index, 0 ≤ fs4SobolevWeight 4 k * ‖c k‖ ^ 2 :=
    fun k => mul_nonneg (fs4SobolevWeight_nonneg 4 k) (sq_nonneg _)
  have hnn3 : ∀ k : FS4Index, 0 ≤ fs4SobolevWeight 3 k * ‖c k‖ ^ 2 :=
    fun k => mul_nonneg (fs4SobolevWeight_nonneg 3 k) (sq_nonneg _)
  have hle : ∀ k : FS4Index,
      fs4SobolevWeight 4 k * ‖c k‖ ^ 2 ≤ fs4SobolevWeight 3 k * ‖c k‖ ^ 2 :=
    fun k => mul_le_mul_of_nonneg_right (fs4_weight_four_le_three k) (sq_nonneg _)
  have hE : (∑' k : FS4Index,
      ENNReal.ofReal (fs4SobolevWeight 4 k * ‖c k‖ ^ 2)) ≤
      ∑' k : FS4Index,
        ENNReal.ofReal (fs4SobolevWeight 3 k * ‖c k‖ ^ 2) :=
    ENNReal.tsum_le_tsum (fun k => ENNReal.ofReal_le_ofReal (hle k))
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn4 hsum4,
      ← ENNReal.ofReal_tsum_of_nonneg hnn3 hc] at hE
  have hreal :
      (∑' k : FS4Index, fs4SobolevWeight 4 k * ‖c k‖ ^ 2) ≤
        ∑' k : FS4Index, fs4SobolevWeight 3 k * ‖c k‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hnn3)).mp hE
  rw [fs4HminusFourEmbedding_norm_eq c hc4]
  unfold fs4HminusFourNorm fs4HminusThreeNorm
  exact Real.sqrt_le_sqrt hreal

theorem fs4_lp_fourier_projection_error_sq_eq_tail
    (K : Finset FS4Index) (x : FS4HminusFourCompletion) :
    ‖x - fs4HminusFourFiniteProjection K (fun k => x (k : FS4Index))‖ ^ (2 : ℝ) =
      ∑' k : FS4Index, if k ∉ K then ‖x k‖ ^ 2 else 0 := by
  let hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hsum : Summable (fun k : FS4Index => ‖x k‖ ^ (2 : ℝ)) :=
    (lp.memℓp x).summable hp
  have hsplit := hsum.sum_add_tsum_compl (s := K)
  have hnormx := lp.norm_rpow_eq_tsum hp x
  have hnormdiff := lp.norm_compl_sum_single hp x K
  have htail :
      (∑' k : FS4Index, if k ∉ K then ‖x k‖ ^ 2 else 0) =
        ∑' j : {k : FS4Index // k ∈ (↑K : Set FS4Index)ᶜ}, ‖x j‖ ^ (2 : ℝ) := by
    calc
      (∑' k : FS4Index, if k ∉ K then ‖x k‖ ^ 2 else 0) =
          ∑' k : FS4Index, ((↑K : Set FS4Index)ᶜ).indicator
            (fun k => ‖x k‖ ^ 2) k := by
        congr 1
        funext k
        by_cases hk : k ∈ K <;> simp [Set.indicator, hk]
      _ = ∑' j : {k : FS4Index // k ∈ (↑K : Set FS4Index)ᶜ},
            ‖x j‖ ^ (2 : ℝ) := (tsum_subtype _ _).symm
  simp only [ENNReal.toReal_ofNat] at hnormx hnormdiff
  have hnormdiff' :
      ‖x - fs4HminusFourFiniteProjection K (fun k => x (k : FS4Index))‖ ^ (2 : ℝ) =
        ‖x‖ ^ (2 : ℝ) - ∑ k ∈ K, ‖x k‖ ^ (2 : ℝ) := by
    simpa [fs4HminusFourFiniteProjection] using hnormdiff
  calc
    ‖x - fs4HminusFourFiniteProjection K (fun k => x (k : FS4Index))‖ ^ (2 : ℝ) =
        ‖x‖ ^ (2 : ℝ) - ∑ k ∈ K, ‖x k‖ ^ (2 : ℝ) := hnormdiff'
    _ = ∑' j : {k : FS4Index // k ∈ (↑K : Set FS4Index)ᶜ},
          ‖x j‖ ^ (2 : ℝ) := by
      rw [hnormx]
      linarith [hsplit]
    _ = ∑' k : FS4Index, if k ∉ K then ‖x k‖ ^ 2 else 0 := htail.symm

def fs4HminusThreeBallInHminusFour (B : ℝ) : Set FS4HminusFourCompletion :=
  {x | ∃ c : FS4Index → ℂ, ∃ hc : c ∈ fs4HminusThreeCoefficientCarrier,
    fs4HminusThreeNorm c ≤ B ∧
      x = fs4HminusFourEmbeddingOfCoefficients c
        (fs4_hminus3_coefficients_in_hminus4 c hc)}

theorem fs4HminusThreeBall_compact_approximation (B : ℝ) (hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Set FS4HminusFourCompletion, IsCompact T ∧
      ∀ x ∈ fs4HminusThreeBallInHminusFour B, ∃ y ∈ T, dist x y < ε := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ := fs4_hminus4_uniform_tail_of_hminus3_bound B hB η hη
  let T := fs4HminusFourFiniteProjection K ''
    {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B}
  have hT : IsCompact T := fs4HminusFourFiniteProjection_boundedBall_compact K B
  refine ⟨T, hT, ?_⟩
  intro x hx
  rcases hx with ⟨c, hc, hcB, rfl⟩
  let h4 := fs4_hminus3_coefficients_in_hminus4 c hc
  let xh := fs4HminusFourEmbeddingOfCoefficients c h4
  let z : {k // k ∈ K} → ℂ := fun k => xh (k : FS4Index)
  have hz : ∀ k, ‖z k‖ ≤ B := by
    intro k
    calc
      ‖z k‖ ≤ ‖xh‖ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) xh _
      _ = fs4HminusFourNorm c := fs4HminusFourEmbedding_norm_eq c h4
      _ ≤ fs4HminusThreeNorm c := by
        calc
          fs4HminusFourNorm c = ‖fs4HminusFourEmbeddingOfCoefficients c h4‖ :=
            (fs4HminusFourEmbedding_norm_eq c h4).symm
          _ ≤ fs4HminusThreeNorm c := fs4HminusFourEmbedding_norm_le_hminusThreeNorm c hc
      _ ≤ B := hcB
  let y := fs4HminusFourFiniteProjection K z
  refine ⟨y, ⟨z, hz, rfl⟩, ?_⟩
  have htail := hK c hc hcB
  let q : ℝ := ∑' k : FS4Index, if k ∉ K then
    fs4SobolevWeight 4 k * ‖c k‖ ^ 2 else 0
  have hq : 0 ≤ q := by
    dsimp [q]
    apply tsum_nonneg
    intro k
    by_cases hk : k ∉ K
    · simp [hk]
      exact mul_nonneg (fs4SobolevWeight_nonneg 4 k) (sq_nonneg _)
    · simp [hk]
  have hqη : Real.sqrt q < η := by
    dsimp [q] at htail ⊢
    exact htail
  have herror_sq : ‖xh - y‖ ^ (2 : ℝ) = q := by
    rw [fs4_lp_fourier_projection_error_sq_eq_tail]
    dsimp [y, z, xh, q]
    apply tsum_congr
    intro k
    by_cases hk : k ∉ K
    · simp only [hk]
      change ‖fs4WeightedFourierCoefficients 4 c k‖ ^ 2 =
        fs4SobolevWeight 4 k * ‖c k‖ ^ 2
      have hw := fs4SobolevWeight_nonneg 4 k
      simp [fs4WeightedFourierCoefficients, Complex.norm_real,
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

theorem fs4_totallyBounded_of_compact_approximation
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

theorem fs4HminusThreeBall_totallyBounded (B : ℝ) (hB : 0 ≤ B) :
    TotallyBounded (fs4HminusThreeBallInHminusFour B) :=
  fs4_totallyBounded_of_compact_approximation
    (fs4HminusThreeBall_compact_approximation B hB)

theorem isCompact_closure_fs4HminusThreeBall (B : ℝ) (hB : 0 ≤ B) :
    IsCompact (closure (fs4HminusThreeBallInHminusFour B)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨(fs4HminusThreeBall_totallyBounded B hB).closure,
    isClosed_closure.isComplete⟩

end Pphi2Clean.Continuum
