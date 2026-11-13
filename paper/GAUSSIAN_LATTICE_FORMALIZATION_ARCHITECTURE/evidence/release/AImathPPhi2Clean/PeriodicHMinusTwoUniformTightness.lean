import AImathPPhi2Clean.PeriodicFullHMinusTwoTraceConcrete
import AImathPPhi2Clean.PeriodicNegativeSobolevTopologyInterfaces

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Extended H^-2 energy of an H^-3 completion point, computed from its
unweighted Fourier coefficients. It is infinite outside the H^-2 domain. -/
def periodicHMinusTwoEnergyOnHMinusThree
    (x : PeriodicHMinusThreeCompletion) : ENNReal :=
  ∑' k : Fin 2 → ℤ, ENNReal.ofReal
    (periodicHMinusTwoFullWeight k *
      ‖periodicHMinusThreeDistributionCoefficients x k‖ ^ 2)

theorem measurable_periodicHMinusTwoEnergyOnHMinusThree :
    Measurable periodicHMinusTwoEnergyOnHMinusThree := by
  apply Measurable.ennreal_tsum
  intro k
  apply ENNReal.measurable_ofReal.comp
  have hcoord : Measurable (fun x : PeriodicHMinusThreeCompletion =>
      periodicHMinusThreeDistributionCoefficients x k) := by
    dsimp [periodicHMinusThreeDistributionCoefficients]
    exact (continuous_periodicHMinusThree_coordinate k).measurable.div_const _
  exact measurable_const.mul (hcoord.norm.pow_const 2)

theorem measurableSet_periodicHMinusTwoEnergySublevel (R : ENNReal) :
    MeasurableSet {x : PeriodicHMinusThreeCompletion |
      periodicHMinusTwoEnergyOnHMinusThree x ≤ R} :=
  measurableSet_le measurable_periodicHMinusTwoEnergyOnHMinusThree measurable_const

theorem measurableSet_periodicHMinusTwoEnergySublevelClosure (R : ENNReal) :
    MeasurableSet (closure {x : PeriodicHMinusThreeCompletion |
      periodicHMinusTwoEnergyOnHMinusThree x ≤ R}) :=
  isClosed_closure.measurableSet

theorem periodicHMinusTwoEnergy_sublevel_mem_ball
    (x : PeriodicHMinusThreeCompletion) (A : ℝ) (hA : 0 ≤ A)
    (henergy : periodicHMinusTwoEnergyOnHMinusThree x ≤ ENNReal.ofReal A) :
    x ∈ periodicHMinusTwoBallInHMinusThree (Real.sqrt A) := by
  let c := periodicHMinusThreeDistributionCoefficients x
  have hterm_nonneg (k : Fin 2 → ℤ) :
      0 ≤ periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2 :=
    mul_nonneg (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _)
  have hfinite : periodicHMinusTwoEnergyOnHMinusThree x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top henergy
  have hsENN : Summable (fun k : Fin 2 → ℤ =>
      (ENNReal.ofReal (periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2)).toReal) :=
    ENNReal.summable_toReal (by simpa [periodicHMinusTwoEnergyOnHMinusThree, c] using hfinite)
  have hs : Summable (fun k : Fin 2 → ℤ =>
      periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) := by
    apply hsENN.congr
    intro k
    exact ENNReal.toReal_ofReal (hterm_nonneg k)
  have hc : c ∈ periodicHMinusTwoCarrier := by
    rw [periodicHMinusTwoCarrier]
    exact hs
  have henergy_eq : periodicHMinusTwoEnergyOnHMinusThree x =
      ENNReal.ofReal (periodicHMinusTwoNorm c ^ 2) := by
    calc
      periodicHMinusTwoEnergyOnHMinusThree x =
          ENNReal.ofReal (∑' k, periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2) := by
        rw [periodicHMinusTwoEnergyOnHMinusThree]
        exact (ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hs).symm
      _ = ENNReal.ofReal (periodicHMinusTwoNorm c ^ 2) := by
        rw [periodicHMinusTwoNorm_sq_eq_fullTrace c hc]
  have hnorm_sq : periodicHMinusTwoNorm c ^ 2 ≤ A := by
    apply (ENNReal.ofReal_le_ofReal_iff hA).mp
    rw [← henergy_eq]
    exact henergy
  have hnorm_sq_root : periodicHMinusTwoNorm c ^ 2 ≤ Real.sqrt A ^ 2 := by
    rw [Real.sq_sqrt hA]
    exact hnorm_sq
  have hnorm_nonneg : 0 ≤ periodicHMinusTwoNorm c := by
    rw [periodicHMinusTwoNorm]
    exact Real.sqrt_nonneg _
  have hnorm : periodicHMinusTwoNorm c ≤ Real.sqrt A :=
    (sq_le_sq₀ hnorm_nonneg (Real.sqrt_nonneg _)).mp hnorm_sq_root
  refine ⟨c, hc, hnorm, ?_⟩
  apply lp.ext
  funext k
  dsimp [periodicHMinusThreeEmbeddingOfHMinusTwo,
    periodicHMinusThreeWeightedCoefficients, c,
    periodicHMinusThreeDistributionCoefficients]
  have hw : 0 < periodicHMinusThreeWeight k := by
    by_cases hk : k = 0
    · simp [periodicHMinusThreeWeight, hk]
    · rw [periodicHMinusThreeWeight, if_neg hk]
      exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hk) _
  have hsqrt : (Real.sqrt (periodicHMinusThreeWeight k) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hw))
  symm
  calc
    (Real.sqrt (periodicHMinusThreeWeight k) : ℂ) *
        (x k / (Real.sqrt (periodicHMinusThreeWeight k) : ℂ)) =
        (x k / (Real.sqrt (periodicHMinusThreeWeight k) : ℂ)) *
          (Real.sqrt (periodicHMinusThreeWeight k) : ℂ) := by ring
    _ = x k := div_mul_cancel₀ _ hsqrt

theorem periodicHMinusTwoEnergy_sublevel_closure_compact
    (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (closure {x : PeriodicHMinusThreeCompletion |
      periodicHMinusTwoEnergyOnHMinusThree x ≤ ENNReal.ofReal R}) := by
  let B := Real.sqrt R
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hball :
      {x : PeriodicHMinusThreeCompletion |
        periodicHMinusTwoEnergyOnHMinusThree x ≤ ENNReal.ofReal R} ⊆
        periodicHMinusTwoBallInHMinusThree B := by
    intro x hx
    simpa [B] using periodicHMinusTwoEnergy_sublevel_mem_ball x R hR hx
  have hcompactBall : IsCompact (closure (periodicHMinusTwoBallInHMinusThree B)) :=
    isCompact_closure_periodicHMinusTwoBallInHMinusThree B hB
  apply hcompactBall.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro x hx
    exact subset_closure (hball hx)
  · exact isClosed_closure

def periodicHMinusTwoRawWeightedSquare (L : ℝ) (hperiod : 0 < L)
    (k : Fin 2 → ℤ)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) : ENNReal :=
  ENNReal.ofReal (periodicHMinusTwoFullWeight k *
    ‖periodicComplexFourierLift L hperiod ω k‖ ^ 2)

theorem measurable_periodicHMinusTwoRawWeightedSquare (L : ℝ)
    (hperiod : 0 < L) (k : Fin 2 → ℤ) :
    Measurable (periodicHMinusTwoRawWeightedSquare L hperiod k) := by
  have hcoord : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
        periodicComplexFourierLift L hperiod ω k) := by
    dsimp [periodicComplexFourierLift, periodicComplexFourierProbe]
    have hcos : Measurable (fun ω : WeakDual ℝ
        (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
          (ω (periodicCosineTest 2 L k hperiod) : ℂ)) :=
      Complex.measurable_ofReal.comp
        ((measurable_pi_apply (periodicCosineTest 2 L k hperiod)).comp
          (comap_measurable _))
    have hsin : Measurable (fun ω : WeakDual ℝ
        (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
          (ω (periodicSineTest 2 L k hperiod) : ℂ)) :=
      Complex.measurable_ofReal.comp
        ((measurable_pi_apply (periodicSineTest 2 L k hperiod)).comp
          (comap_measurable _))
    exact hcos.add (hsin.mul_const Complex.I)
  apply ENNReal.measurable_ofReal.comp
  have hweight : Measurable (fun _ : WeakDual ℝ
      (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
      periodicHMinusTwoFullWeight k) := measurable_const
  exact hweight.mul (hcoord.norm.pow_const 2)

theorem periodicHMinusTwo_lintegral_tsum
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ι → Ω → ENNReal)
    (hf : ∀ k, Measurable (f k)) :
    ∫⁻ ω, ∑' k, f k ω ∂μ = ∑' k, ∫⁻ ω, f k ω ∂μ := by
  rw [lintegral_tsum (fun k => (hf k).aemeasurable)]

theorem periodicHMinusTwo_rawWeightedSquare_tonelli
    (μ : Measure (WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)))
    (L : ℝ) (hperiod : 0 < L) :
    ∫⁻ ω, ∑' k : Fin 2 → ℤ,
      periodicHMinusTwoRawWeightedSquare L hperiod k ω ∂μ =
      ∑' k : Fin 2 → ℤ,
        ∫⁻ ω, periodicHMinusTwoRawWeightedSquare L hperiod k ω ∂μ := by
  exact periodicHMinusTwo_lintegral_tsum μ
    (fun k ω => periodicHMinusTwoRawWeightedSquare L hperiod k ω)
    (fun k => measurable_periodicHMinusTwoRawWeightedSquare L hperiod k)

theorem periodicHMinusTwo_real_tonelli
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (S : Ω → ℝ)
    (hf_meas : ∀ k, Measurable (f k))
    (hf_nonneg : ∀ k ω, 0 ≤ f k ω)
    (hsum : ∀ ω, Summable (fun k => f k ω))
    (hS_eq : S = fun ω => ∑' k, f k ω)
    (hS_int : Integrable S μ)
    (hf_int : ∀ k, Integrable (f k) μ) :
    ∫ ω, S ω ∂μ = ∑' k, ∫ ω, f k ω ∂μ := by
  have hS_nonneg' : ∀ ω, 0 ≤ S ω := by
    intro ω
    rw [hS_eq]
    exact tsum_nonneg (fun k => hf_nonneg k ω)
  have hS_nonneg : 0 ≤ᵐ[μ] S := Filter.Eventually.of_forall hS_nonneg'
  have hof (g : Ω → ℝ) (hg : Integrable g μ) (hgn : 0 ≤ᵐ[μ] g) :
      ENNReal.ofReal (∫ ω, g ω ∂μ) = ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hg hgn
  have hton : ∫⁻ ω, ∑' k, ENNReal.ofReal (f k ω) ∂μ =
      ∑' k, ∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ := by
    simpa only [Function.comp_apply] using
      (lintegral_tsum (fun k => (ENNReal.measurable_ofReal.comp
        (hf_meas k)).aemeasurable : ∀ k, AEMeasurable
          (fun ω => ENNReal.ofReal (f k ω)) μ))
  have hpoint : (fun ω => ENNReal.ofReal (S ω)) =
      (fun ω => ∑' k, ENNReal.ofReal (f k ω)) := by
    funext ω
    rw [hS_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => hf_nonneg k ω)
      (hsum ω)]
  have hmain : ENNReal.ofReal (∫ ω, S ω ∂μ) =
      ∑' k, ENNReal.ofReal (∫ ω, f k ω ∂μ) := by
    rw [hof S hS_int hS_nonneg, hpoint, hton]
    congr 1
    funext k
    exact (hof (f k) (hf_int k)
      (Filter.Eventually.of_forall (hf_nonneg k))).symm
  have hfinite : ∀ k, ENNReal.ofReal (∫ ω, f k ω ∂μ) ≠ ⊤ := by
    intro k
    exact ENNReal.ofReal_ne_top
  have hto := congrArg ENNReal.toReal hmain
  rw [ENNReal.toReal_ofReal (integral_nonneg hS_nonneg')] at hto
  rw [ENNReal.tsum_toReal_eq hfinite] at hto
  apply hto.trans
  congr 1
  funext k
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun ω => hf_nonneg k ω))]

theorem periodic_nonneg_first_moment_tail_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (R : ℝ) (hR : 0 < R)
    (hS : Integrable S μ) (hnonneg : 0 ≤ᵐ[μ] S) :
    μ {ω | R ≤ S ω} ≤ ENNReal.ofReal ((∫ ω, S ω ∂μ) / R) := by
  have hscaled : Integrable (fun ω => S ω / R) μ := hS.div_const R
  have hscaled_nonneg : 0 ≤ᵐ[μ] (fun ω => S ω / R) := by
    filter_upwards [hnonneg] with ω hω
    exact div_nonneg hω (le_of_lt hR)
  calc
    μ {ω | R ≤ S ω} ≤ ENNReal.ofReal (∫ ω, S ω / R ∂μ) := by
      apply hscaled.measure_le_integral hscaled_nonneg
      intro ω hω
      exact (le_div_iff₀ hR).2 (by simpa using hω)
    _ = ENNReal.ofReal ((∫ ω, S ω ∂μ) / R) := by rw [integral_div]

/-- Uniform first-moment control of the extended H^-2 energy gives tightness
of measures on the actual H^-3 completion. The cutoff is `C / ε + 1`, so the
Markov tail is strictly smaller than `ε`; compactness is inherited from the
previous arbitrary-cutoff H^-2-ball closure theorem. -/
theorem periodicHMinusThree_measure_family_tight_of_uniform_HMinusTwo_energy
    (μ : ℕ → Measure PeriodicHMinusThreeCompletion)
    (C : ℝ) (hC : 0 ≤ C)
    (hmoment : ∀ n,
      ∫⁻ x, periodicHMinusTwoEnergyOnHMinusThree x ∂(μ n) ≤ ENNReal.ofReal C) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set PeriodicHMinusThreeCompletion,
      IsCompact K ∧ ∀ n, (μ n) Kᶜ ≤ ENNReal.ofReal ε := by
  intro ε hε
  let T := C / ε + 1
  let A := {x : PeriodicHMinusThreeCompletion |
    periodicHMinusTwoEnergyOnHMinusThree x ≤ ENNReal.ofReal T}
  let K := closure A
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  have hTnonneg : 0 ≤ T := le_of_lt hTpos
  have hratio : C / T < ε := by
    rw [div_lt_iff₀ hTpos]
    have hquot : ε * (C / ε) = C := by field_simp
    dsimp [T]
    nlinarith [hquot, hε]
  have hcompact : IsCompact K := by
    dsimp [K, A]
    exact periodicHMinusTwoEnergy_sublevel_closure_compact T hTnonneg
  refine ⟨K, hcompact, ?_⟩
  intro n
  have hsublevel : A ⊆ K := by
    intro x hx
    exact subset_closure hx
  have hcomplement : Kᶜ ⊆
      {x : PeriodicHMinusThreeCompletion |
        ENNReal.ofReal T ≤ periodicHMinusTwoEnergyOnHMinusThree x} := by
    intro x hx
    have hnot : ¬ periodicHMinusTwoEnergyOnHMinusThree x ≤ ENNReal.ofReal T := by
      intro hle
      exact hx (hsublevel hle)
    exact (lt_of_not_ge hnot).le
  have hmarkov :
      (μ n) {x : PeriodicHMinusThreeCompletion |
        ENNReal.ofReal T ≤ periodicHMinusTwoEnergyOnHMinusThree x} ≤
        (∫⁻ x, periodicHMinusTwoEnergyOnHMinusThree x ∂(μ n)) /
          ENNReal.ofReal T :=
    MeasureTheory.meas_ge_le_lintegral_div (μ := μ n)
      (measurable_periodicHMinusTwoEnergyOnHMinusThree.aemeasurable)
      (ε := ENNReal.ofReal T)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hTpos)) ENNReal.ofReal_ne_top
  calc
    (μ n) Kᶜ ≤ (μ n)
        {x : PeriodicHMinusThreeCompletion |
          ENNReal.ofReal T ≤ periodicHMinusTwoEnergyOnHMinusThree x} :=
      measure_mono hcomplement
    _ ≤ (∫⁻ x, periodicHMinusTwoEnergyOnHMinusThree x ∂(μ n)) /
        ENNReal.ofReal T := hmarkov
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal T :=
      ENNReal.div_le_div_right (hmoment n) _
    _ = ENNReal.ofReal (C / T) := (ENNReal.ofReal_div_of_pos hTpos).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_mono hratio.le

theorem periodicHMinusThree_probabilityMeasure_family_tight_of_uniform_HMinusTwo_energy
    (μ : ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (C : ℝ) (hC : 0 ≤ C)
    (hmoment : ∀ n,
      ∫⁻ x, periodicHMinusTwoEnergyOnHMinusThree x ∂(μ n : Measure _) ≤
        ENNReal.ofReal C) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set PeriodicHMinusThreeCompletion,
      IsCompact K ∧ ∀ n, (μ n : Measure PeriodicHMinusThreeCompletion) Kᶜ ≤
        ENNReal.ofReal ε := by
  exact periodicHMinusThree_measure_family_tight_of_uniform_HMinusTwo_energy
    (fun n => (μ n : Measure PeriodicHMinusThreeCompletion)) C hC hmoment

def periodicHMinusTwoFixedVolumeTraceConstant (L mass : ℝ) : ℝ :=
  mass⁻¹ ^ 2 * L ^ 2 +
    (2 * (mass⁻¹ ^ 2 * L ^ 2)) * ∑' k, periodicHMinusTwoWeight k

theorem periodicHMinusTwo_fixedVolume_trace_bound
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    periodicHMinusTwoFullLiftTrace N a mass L ha hmass hperiod ≤
      periodicHMinusTwoFixedVolumeTraceConstant L mass := by
  exact periodicHMinusTwoFullLiftTrace_concrete_le N a mass L ha hmass hL hperiod

theorem periodicHMinusTwo_fixedVolume_trace_uniform_in_n
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∀ n : ℕ,
      periodicHMinusTwoFullLiftTrace (n + 1) (L / ((n + 1 : ℕ) : ℝ)) mass L
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL ≤
        periodicHMinusTwoFixedVolumeTraceConstant L mass := by
  intro n
  apply periodicHMinusTwo_fixedVolume_trace_bound
    (n + 1) (L / ((n + 1 : ℕ) : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
  field_simp

end Pphi2Clean.Continuum
