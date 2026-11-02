import AImathPPhi2Clean.PeriodicHMinusThreeFourierMeasure
import AImathPPhi2Clean.PeriodicHMinusTwoUniformTightness

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice
open scoped BigOperators

private theorem measurable_periodicHMinusTwoDiscreteRawLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L) :
    Measurable (periodicHMinusTwoDiscreteRawLift N a L hperiod) := by
  rw [measurable_pi_iff]
  intro k
  have hcos : Measurable (fun w : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
      (w (periodicCosineTest 2 L k hperiod) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply (periodicCosineTest 2 L k hperiod)).comp
        (comap_measurable _))
  have hsin : Measurable (fun w : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
      (w (periodicSineTest 2 L k hperiod) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply (periodicSineTest 2 L k hperiod)).comp
        (comap_measurable _))
  have hprobe : Measurable (fun w : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
      periodicComplexFourierLift L hperiod w k) := by
    change Measurable (fun w : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
      (w (periodicCosineTest 2 L k hperiod) : ℂ) +
        (w (periodicSineTest 2 L k hperiod) : ℂ) * Complex.I)
    exact hcos.add (hsin.mul_const Complex.I)
  exact hprobe.comp
    (latticeEmbedLift_measurable (physicalTestEval 2 N a))

private theorem periodicHMinusTwoDiscreteCarrierLift_apply_eq_raw
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (w : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N))) :
    (periodicHMinusTwoDiscreteCarrierLift N a L hperiod w).1 =
      periodicHMinusTwoDiscreteRawLift N a L hperiod w := by
  unfold periodicHMinusTwoDiscreteCarrierLift
  rw [dif_pos (periodicHMinusTwoDiscreteRawLift_mem_carrier N a L ha hperiod w)]

private theorem periodicHMinusTwoDiscreteWeightedSquare_integrable
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (k : Fin 2 → ℤ) :
    Integrable
      (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)) =>
        periodicHMinusTwoFullWeight k *
          ‖periodicHMinusTwoDiscreteRawLift N a L hperiod ω k‖ ^ 2)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass)) := by
  let μ := physicalGJMeasure 2 N a mass ha hmass
  have hcos := physicalGJMeasure_eval_hasGaussianLaw 2 N a mass ha hmass
    (periodicCosineTest 2 L k hperiod)
  have hsin := physicalGJMeasure_eval_hasGaussianLaw 2 N a mass ha hmass
    (periodicSineTest 2 L k hperiod)
  have hcosI : Integrable (fun ω =>
      (ω (periodicCosineTest 2 L k hperiod)) ^ 2) μ :=
    hcos.memLp_two.integrable_sq
  have hsinI : Integrable (fun ω =>
      (ω (periodicSineTest 2 L k hperiod)) ^ 2) μ :=
    hsin.memLp_two.integrable_sq
  have hprobeI : Integrable (fun ω =>
      ‖periodicComplexFourierLift L hperiod ω k‖ ^ 2) μ := by
    have hadd := hcosI.add hsinI
    apply hadd.congr
    filter_upwards [] with ω
    exact (periodicComplexFourierLift_norm_sq L hperiod ω k).symm
  have hphys : Integrable (fun ω =>
      periodicHMinusTwoFullWeight k *
        ‖periodicComplexFourierLift L hperiod ω k‖ ^ 2) μ :=
    hprobeI.const_mul (periodicHMinusTwoFullWeight k)
  have hcomp := hphys.comp_measurable
    (latticeEmbedLift_measurable (physicalTestEval 2 N a))
  simpa [physicalGJMeasure, periodicHMinusTwoDiscreteRawLift,
    periodicHMinusTwoLiftMap, Function.comp_def] using hcomp

private theorem periodicHMinusTwoDiscreteWeightedSquare_integral_eq_moment
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (k : Fin 2 → ℤ) :
    ∫ ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)),
        periodicHMinusTwoFullWeight k *
          ‖periodicHMinusTwoDiscreteRawLift N a L hperiod ω k‖ ^ 2 ∂
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass) =
      periodicHMinusTwoFullWeight k *
        periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k := by
  let μ := physicalGJMeasure 2 N a mass ha hmass
  have hcos := physicalGJMeasure_eval_hasGaussianLaw 2 N a mass ha hmass
    (periodicCosineTest 2 L k hperiod)
  have hsin := physicalGJMeasure_eval_hasGaussianLaw 2 N a mass ha hmass
    (periodicSineTest 2 L k hperiod)
  have hcosI : Integrable (fun ω =>
      (ω (periodicCosineTest 2 L k hperiod)) ^ 2) μ :=
    hcos.memLp_two.integrable_sq
  have hsinI : Integrable (fun ω =>
      (ω (periodicSineTest 2 L k hperiod)) ^ 2) μ :=
    hsin.memLp_two.integrable_sq
  have hprobeI : Integrable (fun ω =>
      ‖periodicComplexFourierLift L hperiod ω k‖ ^ 2) μ := by
    have hadd := hcosI.add hsinI
    apply hadd.congr
    filter_upwards [] with ω
    exact (periodicComplexFourierLift_norm_sq L hperiod ω k).symm
  have hphys : Integrable (fun ω =>
      periodicHMinusTwoFullWeight k *
        ‖periodicComplexFourierLift L hperiod ω k‖ ^ 2) μ :=
    hprobeI.const_mul (periodicHMinusTwoFullWeight k)
  have hmap := integral_map
    (latticeEmbedLift_measurable (physicalTestEval 2 N a)).aemeasurable
    hphys.aestronglyMeasurable
  have hmap' :
      (∫ ω, periodicHMinusTwoFullWeight k *
        ‖periodicComplexFourierLift L hperiod ω k‖ ^ 2 ∂μ) =
      (∫ ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)),
        periodicHMinusTwoFullWeight k *
          ‖periodicHMinusTwoDiscreteRawLift N a L hperiod ω k‖ ^ 2 ∂
        finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 2 N a mass ha hmass)) := by
    simpa [μ, physicalGJMeasure, periodicHMinusTwoDiscreteRawLift,
      periodicHMinusTwoLiftMap, Function.comp_def] using hmap
  rw [← hmap']
  unfold periodicComplexFourierLiftMoment
  rw [← MeasureTheory.integral_const_mul]

theorem periodicHMinusTwoDiscreteLift_integral_eq_fullTrace
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L) (hperiod : 0 < L) :
    ∫ ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)),
        periodicHMinusTwoNorm
          (periodicHMinusTwoDiscreteRawLift N a L hperiod ω) ^ 2 ∂
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass) =
      ∑' k : Fin 2 → ℤ,
        periodicHMinusTwoFullWeight k *
          periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k := by
  let μ := finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 2 N a mass ha hmass)
  let f : (Fin 2 → ℤ) →
      FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)) → ℝ :=
    fun k ω => periodicHMinusTwoFullWeight k *
      ‖periodicHMinusTwoDiscreteRawLift N a L hperiod ω k‖ ^ 2
  let S : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)) → ℝ :=
    fun ω => periodicHMinusTwoNorm
      (periodicHMinusTwoDiscreteRawLift N a L hperiod ω) ^ 2
  have hmem : ∀ ω, periodicHMinusTwoDiscreteRawLift N a L hperiod ω ∈
      periodicHMinusTwoCarrier :=
    fun ω => periodicHMinusTwoDiscreteRawLift_mem_carrier N a L ha hperiod ω
  have hsum : ∀ ω, Summable (fun k => f k ω) := by
    intro ω
    simpa [f, periodicHMinusTwoCarrier] using hmem ω
  have hseq_meas : Measurable
      (periodicHMinusTwoDiscreteRawLift N a L hperiod) :=
    measurable_periodicHMinusTwoDiscreteRawLift N a L hperiod
  have hf_meas : ∀ k, Measurable (f k) := by
    intro k
    dsimp [f]
    have hk : Measurable (fun ω => periodicHMinusTwoDiscreteRawLift N a L hperiod ω k) :=
      (measurable_pi_apply k).comp hseq_meas
    exact measurable_const.mul (hk.norm.pow_const 2)
  have hf_nonneg : ∀ k ω, 0 ≤ f k ω := by
    intro k ω
    exact mul_nonneg (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _)
  have hS_eq : S = fun ω => ∑' k, f k ω := by
    funext ω
    dsimp [S, f]
    exact periodicHMinusTwoNorm_sq_eq_fullTrace _ (hmem ω)
  have hf_int : ∀ k, Integrable (f k) μ := by
    intro k
    simpa [μ, f] using
      (periodicHMinusTwoDiscreteWeightedSquare_integrable
        N a mass L ha hmass hperiod k)
  have hS_int : Integrable S μ := by
    rw [hS_eq]
    have hfm : AEStronglyMeasurable
        (fun ω => ∑' k, f k ω) μ := by
      exact (Measurable.tsum hf_meas).aestronglyMeasurable
    have hnonneg : 0 ≤ᵐ[μ] (fun ω => ∑' k, f k ω) :=
      Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun k => hf_nonneg k ω))
    apply (lintegral_ofReal_ne_top_iff_integrable hfm hnonneg).mp
    have hof : (fun ω => ENNReal.ofReal (∑' k, f k ω)) =
        (fun ω => ∑' k, ENNReal.ofReal (f k ω)) := by
      funext ω
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hf_nonneg k ω) (hsum ω)]
    rw [hof, periodicHMinusTwo_lintegral_tsum μ
        (fun k ω => ENNReal.ofReal (f k ω))
        (fun k => (hf_meas k).ennreal_ofReal)]
    have hlin : (fun k => ∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ) =
        (fun k => ENNReal.ofReal (∫ ω, f k ω ∂μ)) := by
      funext k
      exact (ofReal_integral_eq_lintegral_ofReal (hf_int k)
        (Filter.Eventually.of_forall (hf_nonneg k))).symm
    rw [hlin]
    have hsumMom := periodicHMinusTwoFullLiftTrace_concrete_summable
      N a mass L ha hmass hL hperiod
    have heq : (∑' k, ENNReal.ofReal (∫ ω, f k ω ∂μ)) =
        (∑' k, ENNReal.ofReal
          (periodicHMinusTwoFullWeight k *
            periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k)) := by
      congr 1
      funext k
      rw [periodicHMinusTwoDiscreteWeightedSquare_integral_eq_moment
        N a mass L ha hmass hperiod k]
    rw [heq]
    exact hsumMom.tsum_ofReal_ne_top
  have hton := periodicHMinusTwo_real_tonelli μ f S hf_meas hf_nonneg hsum
    hS_eq hS_int hf_int
  rw [show μ = finiteCovarianceGaussianMeasure
      (numberedLatticeCovarianceGJ 2 N a mass ha hmass) by rfl] at hton
  calc
    _ = ∑' k, ∫ ω, f k ω ∂μ := hton
    _ = ∑' k, periodicHMinusTwoFullWeight k *
        periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k := by
      congr 1
      funext k
      exact periodicHMinusTwoDiscreteWeightedSquare_integral_eq_moment
        N a mass L ha hmass hperiod k

theorem periodicHMinusTwoDiscreteRawNormSq_integrable
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    Integrable
      (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)) =>
        periodicHMinusTwoNorm
          (periodicHMinusTwoDiscreteRawLift N a L hperiod ω) ^ 2)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass)) := by
  let μ := finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 2 N a mass ha hmass)
  let f : (Fin 2 → ℤ) →
      FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)) → ℝ :=
    fun k ω => periodicHMinusTwoFullWeight k *
      ‖periodicHMinusTwoDiscreteRawLift N a L hperiod ω k‖ ^ 2
  let S : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)) → ℝ :=
    fun ω => periodicHMinusTwoNorm
      (periodicHMinusTwoDiscreteRawLift N a L hperiod ω) ^ 2
  have hmem : ∀ ω, periodicHMinusTwoDiscreteRawLift N a L hperiod ω ∈
      periodicHMinusTwoCarrier :=
    fun ω => periodicHMinusTwoDiscreteRawLift_mem_carrier N a L ha hperiod ω
  have hsum : ∀ ω, Summable (fun k => f k ω) := by
    intro ω
    simpa [f, periodicHMinusTwoCarrier] using hmem ω
  have hseq_meas : Measurable
      (periodicHMinusTwoDiscreteRawLift N a L hperiod) :=
    measurable_periodicHMinusTwoDiscreteRawLift N a L hperiod
  have hf_meas : ∀ k, Measurable (f k) := by
    intro k
    dsimp [f]
    have hk : Measurable (fun ω => periodicHMinusTwoDiscreteRawLift N a L hperiod ω k) :=
      (measurable_pi_apply k).comp hseq_meas
    exact measurable_const.mul (hk.norm.pow_const 2)
  have hf_nonneg : ∀ k ω, 0 ≤ f k ω := by
    intro k ω
    exact mul_nonneg (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _)
  have hS_eq : S = fun ω => ∑' k, f k ω := by
    funext ω
    dsimp [S, f]
    exact periodicHMinusTwoNorm_sq_eq_fullTrace _ (hmem ω)
  have hf_int : ∀ k, Integrable (f k) μ := by
    intro k
    simpa [μ, f] using
      (periodicHMinusTwoDiscreteWeightedSquare_integrable
        N a mass L ha hmass hperiod k)
  have hS_int : Integrable S μ := by
    rw [hS_eq]
    have hfm : AEStronglyMeasurable
        (fun ω => ∑' k, f k ω) μ :=
      (Measurable.tsum hf_meas).aestronglyMeasurable
    have hnonneg : 0 ≤ᵐ[μ] (fun ω => ∑' k, f k ω) :=
      Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun k => hf_nonneg k ω))
    apply (lintegral_ofReal_ne_top_iff_integrable hfm hnonneg).mp
    have hof : (fun ω => ENNReal.ofReal (∑' k, f k ω)) =
        (fun ω => ∑' k, ENNReal.ofReal (f k ω)) := by
      funext ω
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hf_nonneg k ω) (hsum ω)]
    rw [hof, periodicHMinusTwo_lintegral_tsum μ
        (fun k ω => ENNReal.ofReal (f k ω))
        (fun k => (hf_meas k).ennreal_ofReal)]
    have hlin : (fun k => ∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ) =
        (fun k => ENNReal.ofReal (∫ ω, f k ω ∂μ)) := by
      funext k
      exact (ofReal_integral_eq_lintegral_ofReal (hf_int k)
        (Filter.Eventually.of_forall (hf_nonneg k))).symm
    rw [hlin]
    have hsumMom := periodicHMinusTwoFullLiftTrace_concrete_summable
      N a mass L ha hmass hL hperiod
    have heq : (∑' k, ENNReal.ofReal (∫ ω, f k ω ∂μ)) =
        (∑' k, ENNReal.ofReal
          (periodicHMinusTwoFullWeight k *
            periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k)) := by
      congr 1
      funext k
      rw [periodicHMinusTwoDiscreteWeightedSquare_integral_eq_moment
        N a mass L ha hmass hperiod k]
    rw [heq]
    exact hsumMom.tsum_ofReal_ne_top
  simpa [μ, S] using hS_int

theorem periodicHMinusTwoDiscreteCarrierLift_integral_eq_fullTrace
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    ∫ ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)),
        periodicHMinusTwoNorm
          (periodicHMinusTwoDiscreteCarrierLift N a L hperiod ω).1 ^ 2 ∂
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass) =
      ∑' k : Fin 2 → ℤ,
        periodicHMinusTwoFullWeight k *
          periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k := by
  have hseq : (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 2 N)) =>
        (periodicHMinusTwoDiscreteCarrierLift N a L hperiod ω).1) =
      (fun ω => periodicHMinusTwoDiscreteRawLift N a L hperiod ω) := by
    funext ω
    exact periodicHMinusTwoDiscreteCarrierLift_apply_eq_raw
      N a L ha hperiod ω
  calc
    _ = ∫ ω, periodicHMinusTwoNorm
        (periodicHMinusTwoDiscreteRawLift N a L hperiod ω) ^ 2 ∂
          finiteCovarianceGaussianMeasure
            (numberedLatticeCovarianceGJ 2 N a mass ha hmass) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact congrArg (fun c : (Fin 2 → ℤ) → ℂ => periodicHMinusTwoNorm c ^ 2)
        (periodicHMinusTwoDiscreteCarrierLift_apply_eq_raw
          N a L ha hperiod ω)
    _ = _ := periodicHMinusTwoDiscreteLift_integral_eq_fullTrace
      N a mass L ha hmass hL hperiod

theorem periodicHMinusTwoDiscreteCarrierLift_fixedVolume_uniform_moment
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∀ n : ℕ,
      ∫ ω : FiniteLatticeConfiguration
          (Fintype.card (FinLatticeSites 2 (n + 1))),
          periodicHMinusTwoNorm
            (periodicHMinusTwoDiscreteCarrierLift (n + 1)
              (L / ((n + 1 : ℕ) : ℝ)) L hL ω).1 ^ 2 ∂
        finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 2 (n + 1)
            (L / ((n + 1 : ℕ) : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass) ≤
        periodicHMinusTwoFixedVolumeTraceConstant L mass := by
  intro n
  have hvol : (L / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) = L := by
    field_simp
  rw [periodicHMinusTwoDiscreteCarrierLift_integral_eq_fullTrace
    (n + 1) (L / ((n + 1 : ℕ) : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hvol hL]
  apply periodicHMinusTwo_fixedVolume_trace_bound
    (n + 1) (L / ((n + 1 : ℕ) : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
  field_simp

theorem periodicHMinusTwoDiscreteCarrierLift_fixedVolume_iSup_moment
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    (⨆ n : ℕ,
      ∫ ω : FiniteLatticeConfiguration
          (Fintype.card (FinLatticeSites 2 (n + 1))),
          periodicHMinusTwoNorm
            (periodicHMinusTwoDiscreteCarrierLift (n + 1)
              (L / ((n + 1 : ℕ) : ℝ)) L hL ω).1 ^ 2 ∂
        finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 2 (n + 1)
            (L / ((n + 1 : ℕ) : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass)) ≤
      periodicHMinusTwoFixedVolumeTraceConstant L mass := by
  apply Real.iSup_le
  · intro n
    exact periodicHMinusTwoDiscreteCarrierLift_fixedVolume_uniform_moment
      L mass hL hmass n
  · have hweight : 0 ≤ ∑' k : Fin 2 → ℤ, periodicHMinusTwoWeight k :=
      tsum_nonneg (fun k => periodicHMinusTwoWeight_nonneg k)
    unfold periodicHMinusTwoFixedVolumeTraceConstant
    positivity

end Pphi2Clean.Continuum
