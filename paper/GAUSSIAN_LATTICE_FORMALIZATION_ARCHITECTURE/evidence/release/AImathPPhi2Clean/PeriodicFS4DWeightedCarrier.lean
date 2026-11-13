import AImathPPhi2Clean.PeriodicFS4DSobolevWeights
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Bases

noncomputable section

namespace Pphi2Clean.Continuum

/-- The completed weighted Fourier sequence spaces underlying the 4D Sobolev carriers. -/
abbrev FS4HminusThreeCompletion := lp (fun _ : FS4Index => ℂ) 2
abbrev FS4HminusFourCompletion := lp (fun _ : FS4Index => ℂ) 2

def fs4WeightedFourierCoefficients (s : ℝ) (c : FS4Index → ℂ) : FS4Index → ℂ :=
  fun k => (Real.sqrt (fs4SobolevWeight s k) : ℂ) * c k

def fs4HminusThreeCoefficientCarrier : Set (FS4Index → ℂ) :=
  {c | Summable (fun k => fs4SobolevWeight 3 k * ‖c k‖ ^ 2)}

def fs4HminusFourCoefficientCarrier : Set (FS4Index → ℂ) :=
  {c | Summable (fun k => fs4SobolevWeight 4 k * ‖c k‖ ^ 2)}

theorem fs4_weight_four_le_three (k : FS4Index) :
    fs4SobolevWeight 4 k ≤ fs4SobolevWeight 3 k := by
  unfold fs4SobolevWeight
  have hnorm : 0 ≤ ‖(fs4SplitIndex k).1‖ := norm_nonneg _
  have hmax : 0 ≤ max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖ :=
    le_trans hnorm (le_max_left _ _)
  have hbase : 1 ≤ 1 + max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖ := by
    linarith
  have hexp : (-2 * (4 : ℝ)) ≤ (-2 * (3 : ℝ)) := by norm_num
  exact Real.rpow_le_rpow_of_exponent_le hbase hexp

theorem fs4_weighted_coefficients_memLp2 (s : ℝ) (c : FS4Index → ℂ)
    (hc : Summable (fun k => fs4SobolevWeight s k * ‖c k‖ ^ 2)) :
    Memℓp (fs4WeightedFourierCoefficients s c) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  change Summable (fun k =>
    ‖(Real.sqrt (fs4SobolevWeight s k) : ℂ) * c k‖ ^ (2 : ℝ))
  apply hc.congr
  intro k
  have hw := fs4SobolevWeight_nonneg s k
  simp [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt hw]

def fs4HminusThreeEmbeddingOfCoefficients (c : FS4Index → ℂ)
    (hc : c ∈ fs4HminusThreeCoefficientCarrier) : FS4HminusThreeCompletion :=
  ⟨fs4WeightedFourierCoefficients 3 c,
    fs4_weighted_coefficients_memLp2 3 c hc⟩

def fs4HminusFourEmbeddingOfCoefficients (c : FS4Index → ℂ)
    (hc : c ∈ fs4HminusFourCoefficientCarrier) : FS4HminusFourCompletion :=
  ⟨fs4WeightedFourierCoefficients 4 c,
    fs4_weighted_coefficients_memLp2 4 c hc⟩

theorem fs4_hminus3_coefficients_in_hminus4 (c : FS4Index → ℂ)
    (hc : c ∈ fs4HminusThreeCoefficientCarrier) :
    c ∈ fs4HminusFourCoefficientCarrier := by
  change Summable (fun k => fs4SobolevWeight 4 k * ‖c k‖ ^ 2)
  change Summable (fun k => fs4SobolevWeight 3 k * ‖c k‖ ^ 2) at hc
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (fs4SobolevWeight_nonneg 4 k) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right (fs4_weight_four_le_three k) (sq_nonneg _)) hc

theorem fs4HminusFour_coordinate_continuous (k : FS4Index) :
    Continuous (fun x : FS4HminusFourCompletion => x k) := by
  exact (lp.evalCLM ℝ (fun _ : FS4Index => ℂ) 2 k).continuous

def fs4HminusFourFiniteProjection (K : Finset FS4Index)
    (z : {k // k ∈ K} → ℂ) : FS4HminusFourCompletion :=
  ∑ k : {k // k ∈ K}, lp.single (E := fun _ : FS4Index => ℂ)
    2 (k : FS4Index) (z k)

theorem fs4HminusFourFiniteProjection_continuous (K : Finset FS4Index) :
    Continuous (fs4HminusFourFiniteProjection K) := by
  apply continuous_finsetSum
  intro k hk
  exact (lp.singleContinuousAddMonoidHom
    (fun _ : FS4Index => ℂ) 2 (k : FS4Index)).continuous.comp
      (continuous_apply k)

theorem fs4HminusFourFiniteProjection_boundedBall_compact
    (K : Finset FS4Index) (B : ℝ) :
    IsCompact (fs4HminusFourFiniteProjection K ''
      {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B}) := by
  have hpi : IsCompact {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B} := by
    convert (isCompact_pi_infinite (fun _ : {k // k ∈ K} =>
      isCompact_closedBall (0 : ℂ) B)) using 1
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  exact hpi.image (fs4HminusFourFiniteProjection_continuous K)


theorem fs4SobolevWeight_neg (s : ℝ) (k : FS4Index) :
    fs4SobolevWeight s (fun i => -k i) = fs4SobolevWeight s k := by
  have h := congrArg (fun q : FS4PairIndex =>
    max ‖q.1‖ ‖q.2‖) (show fs4SplitIndex (fun i => -k i) =
      (-((fs4SplitIndex k).1), -((fs4SplitIndex k).2)) by ext <;> rfl)
  simp only [norm_neg] at h
  unfold fs4SobolevWeight
  exact congrArg (fun x : ℝ => (1 + x) ^ (-2 * s)) h
end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

theorem fs4HminusFour_finite_truncations_approx
    (x : FS4HminusFourCompletion) {eps : ℝ} (heps : 0 < eps) :
    ∃ s : Finset FS4Index,
      ‖x - ∑ i ∈ s, lp.single (E := fun _ : FS4Index => ℂ) 2 i (x i)‖ < eps := by
  have hs : HasSum (fun i : FS4Index =>
      lp.single (E := fun _ : FS4Index => ℂ) 2 i (x i)) x :=
    lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
  rw [HasSum, Metric.tendsto_nhds] at hs
  rcases Filter.eventually_atTop.1 (hs eps heps) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  have hdist := hs s (le_rfl)
  simpa [dist_eq_norm, norm_sub_rev] using hdist

def fs4HminusFourFiniteSupportSum
    (v : Σ s : Finset FS4Index, ({i // i ∈ s} → ℂ)) : FS4HminusFourCompletion :=
  fs4HminusFourFiniteProjection v.1 v.2

theorem fs4HminusFourFiniteSupportSum_continuous :
    Continuous fs4HminusFourFiniteSupportSum := by
  apply continuous_sigma
  intro s
  exact fs4HminusFourFiniteProjection_continuous s

theorem fs4HminusFourFiniteSupportSum_denseRange :
    DenseRange fs4HminusFourFiniteSupportSum := by
  rw [Metric.denseRange_iff]
  intro x eps heps
  obtain ⟨s, hs⟩ := fs4HminusFour_finite_truncations_approx x heps
  refine ⟨⟨s, fun i => x i⟩, ?_⟩
  simpa [dist_eq_norm, fs4HminusFourFiniteSupportSum,
    fs4HminusFourFiniteProjection] using hs

theorem fs4HminusFourCompletion_separable :
    TopologicalSpace.SeparableSpace FS4HminusFourCompletion := by
  have hdense : Dense (Set.range fs4HminusFourFiniteSupportSum) :=
    fs4HminusFourFiniteSupportSum_denseRange
  have hsep : TopologicalSpace.IsSeparable (Set.range fs4HminusFourFiniteSupportSum) :=
    TopologicalSpace.isSeparable_range fs4HminusFourFiniteSupportSum_continuous
  exact (hdense.isSeparable_iff).mp hsep
end Pphi2Clean.Continuum
