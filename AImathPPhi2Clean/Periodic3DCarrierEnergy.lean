import AImathPPhi2Clean.Periodic3DWeightedFiniteSource
import AImathPPhi2Clean.Periodic3DProbeMoment
import AImathPPhi2Clean.PhysicalLatticeGaussianLaw

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

theorem periodic3DFiniteSourceFourierLift_norm_sq (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    ‖periodic3DFiniteSourceFourierLift N a L ω‖ ^ 2 =
      ∑' k : Periodic3DIndex, periodic3DHminusFourWeight k *
        ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal)
    (periodic3DFiniteSourceFourierLift N a L ω)
  norm_num at hnorm
  rw [hnorm]
  apply tsum_congr
  intro k
  have hraw := congrFun
    (periodic3DRawWeightedLift_eq_finiteSourceFourierLift N a L ha hL ω) k
  rw [← hraw]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt (periodic3DHminusFourWeight_nonneg k)]

theorem periodic3DRawAtomicLift_integral_norm_sq_eq_probeMoment
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) (k : Periodic3DIndex) :
    ∫ ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)),
      ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2 ∂
        finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 3 N a mass ha hmass) =
      periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k := by
  let μ := physicalGJMeasure 3 N a mass ha hmass
  have hcosLaw := physicalGJMeasure_eval_hasGaussianLaw 3 N a mass ha hmass
    (periodicCosineTest 3 L k hL)
  have hsinLaw := physicalGJMeasure_eval_hasGaussianLaw 3 N a mass ha hmass
    (periodicSineTest 3 L k hL)
  have hcosInt : Integrable (fun ω =>
      (ω (periodicCosineTest 3 L k hL)) ^ 2) μ := hcosLaw.memLp_two.integrable_sq
  have hsinInt : Integrable (fun ω =>
      (ω (periodicSineTest 3 L k hL)) ^ 2) μ := hsinLaw.memLp_two.integrable_sq
  have hprobeI : Integrable (fun ω =>
      ‖periodic3DComplexFourierProbe L hL k ω‖ ^ 2) μ := by
    have hadd := hcosInt.add hsinInt
    apply hadd.congr
    filter_upwards [] with ω
    exact (periodic3DComplexFourierProbe_norm_sq L hL k ω).symm
  have hmap := integral_map
    (latticeEmbedLift_measurable (physicalTestEval 3 N a)).aemeasurable
    hprobeI.aestronglyMeasurable
  change (∫ ω, ‖periodic3DComplexFourierProbe L hL k
      (latticeEmbedLift (physicalTestEval 3 N a) ω)‖ ^ 2 ∂
        finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) =
    ∫ ω, ‖periodic3DComplexFourierProbe L hL k ω‖ ^ 2 ∂μ
  exact hmap.symm

set_option maxHeartbeats 1000000 in
theorem periodic3DFiniteSourceFourierLift_integrable_norm_sq
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
      ‖periodic3DFiniteSourceFourierLift N a L ω‖ ^ 2)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) := by
  let T := numberedLatticeCovarianceGJ 3 N a mass ha hmass
  let μ := finiteCovarianceGaussianMeasure T
  have hcoord (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
      MemLp (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
        ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N)))) 2 μ := by
    have hg := finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T
      (Pi.single j (1 : ℝ))
    exact hg.memLp_two
  have hsum : MemLp (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 3 N)) =>
      ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℝ) •
          periodic3DSiteVector N a L j) 2 μ := by
    have hsum' : MemLp (∑ j ∈ (Finset.univ : Finset
        (Fin (Fintype.card (FinLatticeSites 3 N)))),
        fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
          (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) : ℝ) •
            periodic3DSiteVector N a L j) 2 μ := by
      apply MeasureTheory.memLp_finsetSum'
      intro j hj
      have hconst : MemLp (fun _ : FiniteLatticeConfiguration
          (Fintype.card (FinLatticeSites 3 N)) =>
            periodic3DSiteVector N a L j) ⊤ μ := memLp_const _
      exact hconst.smul (hcoord j)
    convert hsum' using 1
    ext ω
    simp [Finset.sum_apply]
  change Integrable (fun ω : FiniteLatticeConfiguration
    (Fintype.card (FinLatticeSites 3 N)) =>
      ‖periodic3DFiniteSourceFourierLift N a L ω‖ ^ 2) μ
  have hmap : MemLp (periodic3DFiniteSourceFourierLift N a L) 2 μ := by
    change MemLp (fun ω => periodic3DFiniteSourceCoefficientMap N a L
      (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
        (Fintype.card (FinLatticeSites 3 N)))) ) 2 μ
    unfold periodic3DFiniteSourceCoefficientMap
    convert hsum using 1
  exact hmap.integrable_norm_pow'

theorem periodic3DRawAtomicLift_integral_tsum_three
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∑' k : Periodic3DIndex, ∫ ω,
      periodic3DHminusThreeWeight k * ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) =
    ∫ ω, ∑' k : Periodic3DIndex,
      periodic3DHminusThreeWeight k * ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2
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
      change _ = ‖periodic3DComplexFourierProbe L hL k (latticeEmbedLift (physicalTestEval 3 N a) ω)‖ ^ 2
      rw [periodic3DComplexFourierProbe_norm_sq, latticeEmbedLift_eval_eq, latticeEmbedLift_eval_eq]
    exact hp.const_mul _
  · have ht := (periodic3DComplexFourierProbe_weighted_trace_bound N a mass L ha hmass hvol hL).1
    apply ht.congr
    intro k
    rw [← periodic3DRawAtomicLift_integral_norm_sq_eq_probeMoment N a mass L ha hmass hL k]
    rw [← integral_const_mul]
    congr 1
    funext ω
    exact ((Real.norm_eq_abs _).trans (abs_of_nonneg
      (mul_nonneg (periodic3DHminusThreeWeight_nonneg k) (sq_nonneg _)))).symm

theorem periodic3DRawAtomicLift_integral_energy_three_le
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∫ ω, ∑' k : Periodic3DIndex,
      periodic3DHminusThreeWeight k * ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) ≤
      2 * (mass⁻¹ ^ 2 * L ^ 3) * ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k := by
  rw [← periodic3DRawAtomicLift_integral_tsum_three N a mass L ha hmass hvol hL]
  calc
    _ = ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k *
        periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k := by
      apply tsum_congr
      intro k
      rw [integral_const_mul,
        periodic3DRawAtomicLift_integral_norm_sq_eq_probeMoment N a mass L ha hmass hL k]
    _ ≤ _ := (periodic3DComplexFourierProbe_weighted_trace_bound N a mass L ha hmass hvol hL).2

theorem periodic3DSiteSequence_mem_carrier_three (N : ℕ) [NeZero N]
    (a L : ℝ) (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DSiteSequence N a L j ∈ periodic3DCarrier 3 := by
  rw [periodic3DCarrier]
  have hmajor : Summable (fun k : Periodic3DIndex =>
      a ^ 6 * periodic3DHminusThreeWeight k) :=
    periodic3DHminusThreeWeight_summable.mul_left (a ^ 6)
  apply hmajor.of_nonneg_of_le
  · intro k
    exact mul_nonneg (periodic3DHminusThreeWeight_nonneg k) (sq_nonneg _)
  · intro k
    let θ := periodic3DSitePhase N a L j k
    have hnorm : ‖periodic3DSiteSequence N a L j k‖ ^ 2 = a ^ 6 := by
      dsimp [periodic3DSiteSequence, θ]
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      calc
        (a ^ 3 * Real.cos (periodic3DSitePhase N a L j k)) ^ 2 +
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) ^ 2 =
            a ^ 6 * (Real.cos (periodic3DSitePhase N a L j k) ^ 2 +
              Real.sin (periodic3DSitePhase N a L j k) ^ 2) := by ring
        _ = a ^ 6 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    rw [hnorm]
    exact (mul_comm _ _).le

theorem periodic3DRawAtomicLift_mem_carrier_three (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DRawAtomicLift N a L hL ω ∈ periodic3DCarrier 3 := by
  have hcos (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω)
          (periodicCosineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.cos (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicCosineTest_apply 3 N a L ha k hL j]
    rfl
  have hsin (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω)
          (periodicSineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 3 N a L ha k hL j]
    rfl
  have hseq : periodic3DRawAtomicLift N a L hL ω =
      fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
          periodic3DSiteSequence N a L j k := by
    funext k
    simp only [periodic3DRawAtomicLift, periodic3DComplexFourierLift]
    rw [hcos k, hsin k]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
      Complex.ofReal_sin, periodic3DSiteSequence]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hseq, periodic3DCarrier]
  let s : Finset (Fin (Fintype.card (FinLatticeSites 3 N))) := Finset.univ
  let c : Fin (Fintype.card (FinLatticeSites 3 N)) → ℝ := fun j =>
    ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N)))
  let v : Fin (Fintype.card (FinLatticeSites 3 N)) → Periodic3DIndex → ℂ :=
    fun j => periodic3DSiteSequence N a L j
  let m : ℕ := s.card
  change Summable (fun k : Periodic3DIndex => periodic3DHminusThreeWeight k *
    ‖∑ j ∈ s, (c j : ℂ) * v j k‖ ^ 2)
  have hsum : Summable (fun k : Periodic3DIndex =>
      ∑ j ∈ s, ‖c j‖ ^ 2 *
        (periodic3DHminusThreeWeight k * ‖v j k‖ ^ 2)) := by
    apply summable_sum
    intro j hj
    exact Summable.mul_left (‖c j‖ ^ 2)
      (periodic3DSiteSequence_mem_carrier_three N a L j)
  have hmaj : Summable (fun k : Periodic3DIndex =>
      (m : ℝ) * ∑ j ∈ s, ‖c j‖ ^ 2 *
        (periodic3DHminusThreeWeight k * ‖v j k‖ ^ 2)) :=
    Summable.mul_left (m : ℝ) hsum
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (periodic3DHminusThreeWeight_nonneg k) (sq_nonneg _)
  · intro k
    calc
      periodic3DHminusThreeWeight k * ‖∑ j ∈ s, (c j : ℂ) * v j k‖ ^ 2 ≤
          periodic3DHminusThreeWeight k * (∑ j ∈ s, ‖(c j : ℂ) * v j k‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
            (fun j hj => norm_nonneg _))).2 (norm_sum_le s (fun j => (c j : ℂ) * v j k))
        · exact periodic3DHminusThreeWeight_nonneg k
      _ ≤ periodic3DHminusThreeWeight k *
          ((m : ℝ) * ∑ j ∈ s, ‖(c j : ℂ) * v j k‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq
          (periodic3DHminusThreeWeight_nonneg k)
      _ = (m : ℝ) * ∑ j ∈ s, ‖c j‖ ^ 2 *
          (periodic3DHminusThreeWeight k * ‖v j k‖ ^ 2) := by
        simp [m, mul_pow, Finset.mul_sum, sq_abs]
        ring_nf
  exact hmaj

def periodic3DSiteWeightedSequenceH3 (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) : Periodic3DIndex → ℂ :=
  fun k => (Real.sqrt (periodic3DHminusThreeWeight k) : ℂ) *
    periodic3DSiteSequence N a L j k

theorem periodic3DSiteWeightedSequence_memLpH3 (N : ℕ) [NeZero N]
    (a L : ℝ) (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
    Memℓp (periodic3DSiteWeightedSequenceH3 N a L j) 2 := by
  exact periodic3D_weighted_coefficients_memLp2 3
    (periodic3DSiteSequence N a L j)
    (periodic3DSiteSequence_mem_carrier_three N a L j)

def periodic3DSiteVectorH3 (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) : Periodic3DCompletion :=
  ⟨periodic3DSiteWeightedSequenceH3 N a L j,
    periodic3DSiteWeightedSequence_memLpH3 N a L j⟩

def periodic3DFiniteSourceCoefficientMapH3 (N : ℕ) [NeZero N]
    (a L : ℝ) (c : Fin (Fintype.card (FinLatticeSites 3 N)) → ℝ) :
    Periodic3DCompletion :=
  ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
    c j • periodic3DSiteVectorH3 N a L j

theorem continuous_periodic3DFiniteSourceCoefficientMapH3 (N : ℕ) [NeZero N]
    (a L : ℝ) : Continuous (periodic3DFiniteSourceCoefficientMapH3 N a L) := by
  unfold periodic3DFiniteSourceCoefficientMapH3
  exact continuous_finsetSum Finset.univ (fun j _ =>
    (continuous_apply j).smul continuous_const)

def periodic3DFiniteSourceFourierLiftH3 (N : ℕ) [NeZero N]
    (a L : ℝ)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    Periodic3DCompletion :=
  periodic3DFiniteSourceCoefficientMapH3 N a L
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N))) )

theorem measurable_periodic3DFiniteSourceFourierLiftH3 (N : ℕ) [NeZero N]
    (a L : ℝ) : Measurable (periodic3DFiniteSourceFourierLiftH3 N a L) := by
  unfold periodic3DFiniteSourceFourierLiftH3
  have hcoords : Measurable (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 3 N)) =>
        fun j : Fin (Fintype.card (FinLatticeSites 3 N)) =>
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N)))) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N)))).comp (comap_measurable _)
  exact (continuous_periodic3DFiniteSourceCoefficientMapH3 N a L).measurable.comp hcoords

theorem periodic3DFiniteSourceFourierLift_applyH3 (N : ℕ) [NeZero N]
    (a L : ℝ)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)))
    (k : Periodic3DIndex) :
    periodic3DFiniteSourceFourierLiftH3 N a L ω k =
      ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
          periodic3DSiteWeightedSequenceH3 N a L j k := by
  change (⇑(periodic3DFiniteSourceCoefficientMapH3 N a L
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N)))))) k = _
  rw [periodic3DFiniteSourceCoefficientMapH3, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    periodic3DSiteVectorH3, Complex.real_smul]

theorem periodic3DRawAtomicLift_eq_site_sumH3 (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DRawAtomicLift N a L hL ω =
      fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
          periodic3DSiteSequence N a L j k := by
  have hcos (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω)
          (periodicCosineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.cos (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicCosineTest_apply 3 N a L ha k hL j]
    rfl
  have hsin (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω)
          (periodicSineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 3 N a L ha k hL j]
    rfl
  funext k
  simp only [periodic3DRawAtomicLift, periodic3DComplexFourierLift]
  rw [hcos k, hsin k]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
    Complex.ofReal_sin, periodic3DSiteSequence]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem periodic3DRawWeightedLift_eq_finiteSourceFourierLiftH3 (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    (fun k => (Real.sqrt (periodic3DHminusThreeWeight k) : ℂ) *
        periodic3DRawAtomicLift N a L hL ω k) =
      fun k => periodic3DFiniteSourceFourierLiftH3 N a L ω k := by
  funext k
  rw [periodic3DRawAtomicLift_eq_site_sumH3 N a L ha hL ω]
  rw [periodic3DFiniteSourceFourierLift_applyH3]
  simp only [periodic3DSiteWeightedSequenceH3]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem periodic3DFiniteSourceFourierLiftH3_norm_sq (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    ‖periodic3DFiniteSourceFourierLiftH3 N a L ω‖ ^ 2 =
      ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k *
        ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal)
    (periodic3DFiniteSourceFourierLiftH3 N a L ω)
  norm_num at hnorm
  rw [hnorm]
  apply tsum_congr
  intro k
  have hraw := congrFun
    (periodic3DRawWeightedLift_eq_finiteSourceFourierLiftH3 N a L ha hL ω) k
  rw [← hraw]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt (periodic3DHminusThreeWeight_nonneg k)]

set_option maxHeartbeats 1000000 in
theorem periodic3DFiniteSourceFourierLiftH3_integrable_norm_sq
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
      ‖periodic3DFiniteSourceFourierLiftH3 N a L ω‖ ^ 2)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) := by
  let T := numberedLatticeCovarianceGJ 3 N a mass ha hmass
  let μ := finiteCovarianceGaussianMeasure T
  have hcoord (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
      MemLp (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
        ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N)))) 2 μ := by
    have hg := finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T
      (Pi.single j (1 : ℝ))
    exact hg.memLp_two
  have hsum : MemLp (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 3 N)) =>
      ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℝ) •
          periodic3DSiteVectorH3 N a L j) 2 μ := by
    have hsum' : MemLp (∑ j ∈ (Finset.univ : Finset
        (Fin (Fintype.card (FinLatticeSites 3 N)))),
        fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
          (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) : ℝ) •
            periodic3DSiteVectorH3 N a L j) 2 μ := by
      apply MeasureTheory.memLp_finsetSum'
      intro j hj
      have hconst : MemLp (fun _ : FiniteLatticeConfiguration
          (Fintype.card (FinLatticeSites 3 N)) =>
            periodic3DSiteVectorH3 N a L j) ⊤ μ := memLp_const _
      exact hconst.smul (hcoord j)
    convert hsum' using 1
    ext ω
    simp [Finset.sum_apply]
  change Integrable (fun ω : FiniteLatticeConfiguration
    (Fintype.card (FinLatticeSites 3 N)) =>
      ‖periodic3DFiniteSourceFourierLiftH3 N a L ω‖ ^ 2) μ
  have hmap : MemLp (periodic3DFiniteSourceFourierLiftH3 N a L) 2 μ := by
    change MemLp (fun ω => periodic3DFiniteSourceCoefficientMapH3 N a L
      (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
        (Fintype.card (FinLatticeSites 3 N)))) ) 2 μ
    unfold periodic3DFiniteSourceCoefficientMapH3
    convert hsum using 1
  exact hmap.integrable_norm_pow'

theorem periodic3DFiniteSourceFourierLiftH3_integral_norm_sq_le
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∫ ω, ‖periodic3DFiniteSourceFourierLiftH3 N a L ω‖ ^ 2
      ∂finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) ≤
      2 * (mass⁻¹ ^ 2 * L ^ 3) * ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k := by
  simp_rw [periodic3DFiniteSourceFourierLiftH3_norm_sq N a L ha hL]
  exact periodic3DRawAtomicLift_integral_energy_three_le N a mass L ha hmass hvol hL

theorem periodic3DRawAtomicLift_integrable_energy_three
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) :
    Integrable (fun ω => ∑' k : Periodic3DIndex,
      periodic3DHminusThreeWeight k * ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2)
      (finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) := by
  have h := periodic3DFiniteSourceFourierLiftH3_integrable_norm_sq N a mass L ha hmass
  simpa only [periodic3DFiniteSourceFourierLiftH3_norm_sq N a L ha hL] using h

theorem periodic3DFiniteSourceFourierLiftH3_markov_tail
    (N : ℕ) [NeZero N] (a mass L B : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) (hB : 0 < B) :
    finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)
      {ω | B ^ 2 ≤ ‖periodic3DFiniteSourceFourierLiftH3 N a L ω‖ ^ 2} ≤
      ENNReal.ofReal ((2 * (mass⁻¹ ^ 2 * L ^ 3) *
        ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k) / B ^ 2) := by
  let μ := finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 3 N a mass ha hmass)
  let X := periodic3DFiniteSourceFourierLiftH3 N a L
  have hInt := periodic3DFiniteSourceFourierLiftH3_integrable_norm_sq
    N a mass L ha hmass
  have hSecond := periodic3DFiniteSourceFourierLiftH3_integral_norm_sq_le
    N a mass L ha hmass hL hperiod
  have hScaled : Integrable (fun ω => ‖X ω‖ ^ 2 / B ^ 2) μ := by
    have hmul := hInt.const_mul ((B ^ 2)⁻¹)
    convert hmul using 1
    ext ω
    simp [X, div_eq_mul_inv, mul_comm]
  have hNonneg : 0 ≤ᵐ[μ] (fun ω => ‖X ω‖ ^ 2 / B ^ 2) := by
    filter_upwards [] with ω
    exact div_nonneg (sq_nonneg ‖X ω‖) (sq_nonneg B)
  let s : Set (FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :=
    {ω | B ^ 2 ≤ ‖X ω‖ ^ 2}
  have hMarkov := hScaled.measure_le_integral hNonneg (s := s)
    (by
      intro ω hω
      dsimp [s] at hω ⊢
      exact (le_div_iff₀ (sq_pos_of_pos hB)).2 (by simpa using hω))
  have hIntegral : (∫ ω, ‖X ω‖ ^ 2 / B ^ 2 ∂μ) ≤
      (2 * (mass⁻¹ ^ 2 * L ^ 3) * ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k) / B ^ 2 := by
    have hscale : (∫ ω, ‖X ω‖ ^ 2 / B ^ 2 ∂μ) =
        (B ^ 2)⁻¹ * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
      rw [show (fun ω => ‖X ω‖ ^ 2 / B ^ 2) =
        (fun ω => (B ^ 2)⁻¹ * ‖X ω‖ ^ 2) by
          funext ω
          ring]
      rw [integral_const_mul]
    rw [hscale]
    calc
      (B ^ 2)⁻¹ * ∫ ω, ‖X ω‖ ^ 2 ∂μ ≤
          (B ^ 2)⁻¹ * ((2 * (mass⁻¹ ^ 2 * L ^ 3)) *
            ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k) :=
        mul_le_mul_of_nonneg_left hSecond (inv_nonneg.mpr (sq_nonneg B))
      _ = (2 * (mass⁻¹ ^ 2 * L ^ 3) *
          ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k) / B ^ 2 := by ring
  have hOfReal := ENNReal.ofReal_le_ofReal hIntegral
  change μ s ≤ _ at hMarkov
  rw [show μ = finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 3 N a mass ha hmass) by rfl] at hMarkov
  exact hMarkov.trans hOfReal

theorem periodic3DFiniteSourceFourierLift_norm_le_H3
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    ‖periodic3DFiniteSourceFourierLift N a L ω‖ ≤
      ‖periodic3DFiniteSourceFourierLiftH3 N a L ω‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [periodic3DFiniteSourceFourierLift_norm_sq N a L ha hL,
    periodic3DFiniteSourceFourierLiftH3_norm_sq N a L ha hL]
  apply Summable.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right (periodic3DHminusFourWeight_le_three k) (sq_nonneg _))
  · exact periodic3DRawAtomicLift_mem_carrier N a L ha hL ω
  · exact periodic3DRawAtomicLift_mem_carrier_three N a L ha hL ω

end Pphi2Clean.Continuum




