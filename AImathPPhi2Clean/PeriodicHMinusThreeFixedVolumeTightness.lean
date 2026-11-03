import AImathPPhi2Clean.PeriodicHMinusTwoFiniteSourceTrace

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

/-- The Fourier-defined extended H^-2 energy agrees with the H^-2 norm whenever
its decoded coefficient sequence lies in the H^-2 carrier. -/
theorem periodicHMinusTwoEnergyOnHMinusThree_eq_of_HMinusTwo_coefficients
    (x : PeriodicHMinusThreeCompletion)
    (hc : periodicHMinusThreeDistributionCoefficients x ∈ periodicHMinusTwoCarrier) :
    periodicHMinusTwoEnergyOnHMinusThree x =
      ENNReal.ofReal
        (periodicHMinusTwoNorm (periodicHMinusThreeDistributionCoefficients x) ^ 2) := by
  have hterm (k : PeriodicFourierIndex) :
      0 ≤ periodicHMinusTwoFullWeight k *
        ‖periodicHMinusThreeDistributionCoefficients x k‖ ^ 2 :=
    mul_nonneg (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _)
  have hsum : Summable (fun k : PeriodicFourierIndex =>
      periodicHMinusTwoFullWeight k *
        ‖periodicHMinusThreeDistributionCoefficients x k‖ ^ 2) := by
    simpa [periodicHMinusTwoCarrier] using hc
  calc
    periodicHMinusTwoEnergyOnHMinusThree x =
        ENNReal.ofReal (∑' k, periodicHMinusTwoFullWeight k *
          ‖periodicHMinusThreeDistributionCoefficients x k‖ ^ 2) := by
      unfold periodicHMinusTwoEnergyOnHMinusThree
      exact (ENNReal.ofReal_tsum_of_nonneg hterm hsum).symm
    _ = ENNReal.ofReal
        (periodicHMinusTwoNorm (periodicHMinusThreeDistributionCoefficients x) ^ 2) := by
      rw [periodicHMinusTwoNorm_sq_eq_fullTrace _ hc]

/-- Deweighting the concrete finite-source H^-3 lift recovers exactly the
existing H^-2 lattice Fourier lift, including the `a^2` sampling factor. -/
theorem periodicHMinusThreeFiniteSourceFourierLift_coefficients_eq_discreteRawLift
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N))) :
    periodicHMinusThreeDistributionCoefficients
        (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω) =
      periodicHMinusTwoDiscreteRawLift N a L hperiod ω := by
  funext k
  have hweight : 0 < periodicHMinusThreeWeight k := by
    by_cases hk : k = 0
    · simp [periodicHMinusThreeWeight, hk]
    · rw [periodicHMinusThreeWeight, if_neg hk]
      exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hk) _
  have hsqrt : (Real.sqrt (periodicHMinusThreeWeight k) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hweight))
  have hcoord :
      periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω k =
        (Real.sqrt (periodicHMinusThreeWeight k) : ℂ) *
          periodicHMinusTwoDiscreteRawLift N a L hperiod ω k := by
    have h := congrFun
      (periodicHMinusThreeRawWeightedLift_eq_finiteSourceFourierLift
        N a L ha hperiod ω) k
    simpa [periodicHMinusThreeRawWeightedLift,
      periodicHMinusThreeWeightedCoefficients, periodicHMinusTwoDiscreteRawLift,
      periodicHMinusTwoLiftMap, periodicComplexFourierLift] using h.symm
  simp only [periodicHMinusThreeDistributionCoefficients]
  rw [hcoord]
  exact mul_div_cancel_left₀ _ hsqrt

/-- Pointwise energy identity for the actual finite lattice configuration lift. -/
theorem periodicHMinusThreeFiniteSourceFourierLift_energy_eq_norm_sq
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N))) :
    periodicHMinusTwoEnergyOnHMinusThree
        (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω) =
      ENNReal.ofReal
        (periodicHMinusTwoNorm
          (periodicHMinusTwoDiscreteRawLift N a L hperiod ω) ^ 2) := by
  have hc := periodicHMinusTwoDiscreteRawLift_mem_carrier
    N a L ha hperiod ω
  have hcoeff := periodicHMinusThreeFiniteSourceFourierLift_coefficients_eq_discreteRawLift
    N a L ha hperiod ω
  have hc' : periodicHMinusThreeDistributionCoefficients
      (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω) ∈
        periodicHMinusTwoCarrier := by
    rw [hcoeff]
    exact hc
  calc
    _ = ENNReal.ofReal
        (periodicHMinusTwoNorm
          (periodicHMinusThreeDistributionCoefficients
            (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω)) ^ 2) :=
      periodicHMinusTwoEnergyOnHMinusThree_eq_of_HMinusTwo_coefficients _ hc'
    _ = _ := by rw [hcoeff]

/-- The sequence `N = n + 1`, `a_n = L / (n + 1)` as Borel probability measures
on the concrete periodic H^-3 completion. -/
noncomputable def periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    ProbabilityMeasure PeriodicHMinusThreeCompletion := by
  let N := n + 1
  let a : ℝ := L / ((n + 1 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
  exact ProbabilityMeasure.map
    (⟨finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass), by infer_instance⟩ :
      ProbabilityMeasure (FiniteLatticeConfiguration
        (Fintype.card (FinLatticeSites 2 N))))
    (f := periodicHMinusThreeFiniteSourceFourierLift N a L hL) (measurable_periodicHMinusThreeFiniteSourceFourierLift N a L hL).aemeasurable

/-- The fixed-physical-volume sequence of Borel probability measures, indexed
by n with lattice size N = n + 1 and spacing a_n = L / (n + 1). -/
noncomputable def periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion :=
  fun n => periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
    L mass hL hmass n

/-- The exact weak-limit proposition for a specified candidate Borel
probability measure muFree. This is a statement only; it does not construct
muFree or prove convergence. -/
def periodicHMinusThreeFixedVolumeFreeFieldWeakLimit
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion) : Prop :=
  Filter.Tendsto
    (periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence L mass hL hmass)
    Filter.atTop (nhds μfree)

/-- Existential form of the fixed-volume weak-limit target. A later goal must
construct and identify the limit measure; this proposition is not asserted
here as a theorem. -/
def periodicHMinusThreeFixedVolumeFreeFieldWeakLimitExists
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) : Prop :=
  ∃ μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion,
    periodicHMinusThreeFixedVolumeFreeFieldWeakLimit L mass hL hmass μfree

/-- The probability-measure family is exactly the finite-source pushforward law
already used for the lattice lift. -/
theorem periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure_toMeasure
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
      L mass hL hmass n : Measure PeriodicHMinusThreeCompletion) =
      periodicHMinusThreeFiniteSourceMeasure (n + 1)
        (L / ((n + 1 : ℕ) : ℝ)) mass L
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL := by
  change Measure.map
      (periodicHMinusThreeFiniteSourceFourierLift (n + 1)
        (L / ((n + 1 : ℕ) : ℝ)) L hL)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 (n + 1)
          (L / ((n + 1 : ℕ) : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass)) = _
  exact periodicHMinusThreeFiniteSourceFourierLift_map_eq_finiteSourceMeasure
    (n + 1) (L / ((n + 1 : ℕ) : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL

/-- The fixed-volume pushforward has the exact H^-2 energy lintegral bound
inherited from the finite-source trace estimate. -/
theorem periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure_energy_bound
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    ∫⁻ x, periodicHMinusTwoEnergyOnHMinusThree x ∂
      (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
        L mass hL hmass n : Measure PeriodicHMinusThreeCompletion) ≤
      ENNReal.ofReal (periodicHMinusTwoFixedVolumeTraceConstant L mass) := by
  let N := n + 1
  let a : ℝ := L / ((n + 1 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hLatticeVolume : a * (N : ℝ) = L := by
    dsimp [a, N]
    field_simp
  let μ := finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 2 N a mass ha hmass)
  let lift := periodicHMinusThreeFiniteSourceFourierLift N a L hL
  have hliftMeas : Measurable lift :=
    measurable_periodicHMinusThreeFiniteSourceFourierLift N a L hL
  have henergyMeas : Measurable periodicHMinusTwoEnergyOnHMinusThree :=
    measurable_periodicHMinusTwoEnergyOnHMinusThree
  have hnormIntegrable := periodicHMinusTwoDiscreteRawNormSq_integrable
    N a mass L ha hmass hLatticeVolume hL
  have hrawBound :
      ∫ ω, periodicHMinusTwoNorm
        (periodicHMinusTwoDiscreteRawLift N a L hL ω) ^ 2 ∂μ ≤
        periodicHMinusTwoFixedVolumeTraceConstant L mass := by
    have hcarrierBound := periodicHMinusTwoDiscreteCarrierLift_fixedVolume_uniform_moment
      L mass hL hmass n
    calc
      ∫ ω, periodicHMinusTwoNorm
          (periodicHMinusTwoDiscreteRawLift N a L hL ω) ^ 2 ∂μ =
          ∫ ω, periodicHMinusTwoNorm
            (periodicHMinusTwoDiscreteCarrierLift N a L hL ω).1 ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        have hcarrier := periodicHMinusTwoDiscreteRawLift_mem_carrier
          N a L ha hL ω
        have heq : (periodicHMinusTwoDiscreteCarrierLift N a L hL ω).1 =
            periodicHMinusTwoDiscreteRawLift N a L hL ω := by
          unfold periodicHMinusTwoDiscreteCarrierLift
          rw [dif_pos hcarrier]
        exact congrArg (fun c => periodicHMinusTwoNorm c ^ 2) heq.symm
      _ ≤ periodicHMinusTwoFixedVolumeTraceConstant L mass := by
        simpa [μ, N, a] using hcarrierBound
  have hpoint : ∀ ω,
      periodicHMinusTwoEnergyOnHMinusThree (lift ω) =
        ENNReal.ofReal (periodicHMinusTwoNorm
          (periodicHMinusTwoDiscreteRawLift N a L hL ω) ^ 2) := by
    intro ω
    exact periodicHMinusThreeFiniteSourceFourierLift_energy_eq_norm_sq
      N a mass L ha hmass hL ω
  calc
    ∫⁻ x, periodicHMinusTwoEnergyOnHMinusThree x ∂
        (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
          L mass hL hmass n : Measure PeriodicHMinusThreeCompletion) =
        ∫⁻ ω, periodicHMinusTwoEnergyOnHMinusThree (lift ω) ∂μ := by
      rw [periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure_toMeasure]
      rw [← periodicHMinusThreeFiniteSourceFourierLift_map_eq_finiteSourceMeasure
        N a mass L ha hmass hL]
      exact lintegral_map henergyMeas hliftMeas
    _ = ∫⁻ ω, ENNReal.ofReal (periodicHMinusTwoNorm
          (periodicHMinusTwoDiscreteRawLift N a L hL ω) ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact hpoint ω
    _ = ENNReal.ofReal (∫ ω, periodicHMinusTwoNorm
          (periodicHMinusTwoDiscreteRawLift N a L hL ω) ^ 2 ∂μ) := by
      exact (ofReal_integral_eq_lintegral_ofReal hnormIntegrable
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))).symm
    _ ≤ ENNReal.ofReal (periodicHMinusTwoFixedVolumeTraceConstant L mass) :=
      ENNReal.ofReal_mono hrawBound

/-- The concrete finite-volume lattice free-field laws are tight in H^-3. -/
theorem periodicHMinusThree_fixedVolume_freeField_tight
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set PeriodicHMinusThreeCompletion,
      IsCompact K ∧ ∀ n,
        (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
          L mass hL hmass n : Measure PeriodicHMinusThreeCompletion) Kᶜ ≤
            ENNReal.ofReal ε := by
  have hC : 0 ≤ periodicHMinusTwoFixedVolumeTraceConstant L mass := by
    unfold periodicHMinusTwoFixedVolumeTraceConstant
    have hweight : 0 ≤ ∑' k : Fin 2 → ℤ, periodicHMinusTwoWeight k :=
      tsum_nonneg (fun k => periodicHMinusTwoWeight_nonneg k)
    positivity
  apply periodicHMinusThree_probabilityMeasure_family_tight_of_uniform_HMinusTwo_energy
    (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure L mass hL hmass)
    (periodicHMinusTwoFixedVolumeTraceConstant L mass) hC
  intro n
  exact periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure_energy_bound
    L mass hL hmass n

end Pphi2Clean.Continuum
