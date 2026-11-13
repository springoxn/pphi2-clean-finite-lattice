import AImathPPhi2Clean.Periodic3DAtomicMarginal

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

def periodic3DRestrictIndex (k : FS4Index) : Periodic3DIndex :=
  fun i => k (Fin.castSucc i)

theorem periodic3DExtend_restrictIndex_of_fourth_zero (k : FS4Index)
    (hk : k 3 = 0) : periodic3DExtend (periodic3DRestrictIndex k) = k := by
  funext i
  by_cases hi : i.val < 3
  · have hv : Fin.castSucc (⟨i.val, hi⟩ : Fin 3) = i := by
      apply Fin.ext
      rfl
    simp [periodic3DExtend, periodic3DRestrictIndex, hi, hv]
  · have hi3 : i = 3 := by ext; omega
    subst i
    simp [periodic3DExtend, hk]

def periodic3DCanonicalCoordinateProjection {m : ℕ}
    (js : Fin m → FS4GaussianRealCoordinateIndex) :
    Periodic3DCompletion → EuclideanSpace ℝ (Fin m) := fun x =>
  WithLp.toLp 2 (fun i =>
    (js i).elim (fun _ => (x 0).re) (fun q =>
      let k := periodic3DRestrictIndex q.1.1
      let z := x k / (Real.sqrt (periodic3DHminusFourWeight k) : ℂ)
      if q.2 then z.im else z.re))

theorem continuous_periodic3DCanonicalCoordinateProjection {m : ℕ}
    (js : Fin m → FS4GaussianRealCoordinateIndex) :
    Continuous (periodic3DCanonicalCoordinateProjection js) := by
  unfold periodic3DCanonicalCoordinateProjection
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  rcases js i with u | ⟨k,b⟩
  · exact Complex.continuous_re.comp (periodic3DHminusFour_coordinate_continuous 0)
  · cases b
    · exact Complex.continuous_re.comp
        ((periodic3DHminusFour_coordinate_continuous (periodic3DRestrictIndex k.1)).div_const _)
    · exact Complex.continuous_im.comp
        ((periodic3DHminusFour_coordinate_continuous (periodic3DRestrictIndex k.1)).div_const _)

theorem periodic3DCanonicalCoordinateProjection_targetMap
    {m : ℕ} (L : ℝ) (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0))
    (x : FS4HminusFourCompletion) :
    periodic3DCanonicalCoordinateProjection js (periodic3DTargetMap L x) =
      (Real.sqrt L)⁻¹ • fs4PhysicalFiniteProjection js x := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).injective
  funext i
  simp only [PiLp.continuousLinearEquiv_apply, periodic3DCanonicalCoordinateProjection,
    fs4PhysicalFiniteProjection, WithLp.ofLp_toLp, PiLp.smul_apply]
  rcases hj : js i with u | ⟨k,b⟩
  · change (periodic3DTargetMap L x 0).re =
      (Real.sqrt L)⁻¹ * fs4PhysicalRealCoordinate (Sum.inl u) x
    have hz : periodic3DExtend (0 : Periodic3DIndex) = (0 : FS4Index) := by ext j; fin_cases j <;> simp [periodic3DExtend]
    rw [periodic3DTargetMap_apply, hz]
    congr 1
    norm_num [fs4PhysicalRealCoordinate]
  · have hk0 : k.1 3 = 0 := by simpa [hj] using hsupport i
    have hext := periodic3DExtend_restrictIndex_of_fourth_zero k.1 hk0
    cases b
    · change (periodic3DTargetMap L x (periodic3DRestrictIndex k.1) /
        (Real.sqrt (periodic3DHminusFourWeight (periodic3DRestrictIndex k.1)) : ℂ)).re =
        (Real.sqrt L)⁻¹ * fs4PhysicalRealCoordinate (Sum.inr (k,false)) x
      simp only [periodic3DTargetMap_apply, periodic3DRestrictFourierCLM, periodic3DRestrictFourier, periodic3DHminusFourWeight, periodic3DSobolevWeight]
      rw [hext]
      simp only [fs4PhysicalRealCoordinate, fs4GaussianRealCoordinate, Sum.elim_inr, apply_ite]
      norm_num [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring_nf
    · change (periodic3DTargetMap L x (periodic3DRestrictIndex k.1) /
        (Real.sqrt (periodic3DHminusFourWeight (periodic3DRestrictIndex k.1)) : ℂ)).im =
        (Real.sqrt L)⁻¹ * fs4PhysicalRealCoordinate (Sum.inr (k,true)) x
      simp only [periodic3DTargetMap_apply, periodic3DRestrictFourierCLM, periodic3DRestrictFourier, periodic3DHminusFourWeight, periodic3DSobolevWeight]
      rw [hext]
      simp only [fs4PhysicalRealCoordinate, fs4GaussianRealCoordinate, Sum.elim_inr, apply_ite]
      norm_num [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring_nf

theorem periodic3DGaussianTargetMeasure_map_canonicalProjection
    {m : ℕ} (L mass : ℝ) (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0)) :
    (periodic3DGaussianTargetMeasure L mass).map
        (periodic3DCanonicalCoordinateProjection js) =
      Measure.map (fun z : EuclideanSpace ℝ (Fin m) => (Real.sqrt L)⁻¹ • z)
        (fs4PhysicalFiniteMarginal L mass js) := by
  unfold periodic3DGaussianTargetMeasure fs4PhysicalFiniteMarginal
  rw [Measure.map_map (continuous_periodic3DCanonicalCoordinateProjection js).measurable
    (continuous_periodic3DTargetMap L).measurable]
  have hscale : Continuous (fun z : EuclideanSpace ℝ (Fin m) => (Real.sqrt L)⁻¹ • z) := by
    exact (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin m) => ((Real.sqrt L)⁻¹ : ℝ))).smul continuous_id
  rw [Measure.map_map hscale.measurable (fs4PhysicalFiniteProjection_continuous js).measurable]
  congr 1
  funext x
  exact periodic3DCanonicalCoordinateProjection_targetMap L js hsupport x


theorem periodic3DGaussianTargetMeasure_canonicalProjection_hasGaussianLaw
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (hjs : Function.Injective js)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0)) :
    HasGaussianLaw id
      ((periodic3DGaussianTargetMeasure L mass).map
        (periodic3DCanonicalCoordinateProjection js)) := by
  rw [periodic3DGaussianTargetMeasure_map_canonicalProjection L mass js hsupport]
  let E := EuclideanSpace ℝ (Fin m)
  let c : ℝ := (Real.sqrt L)⁻¹
  let S : E →L[ℝ] E := LinearMap.mkContinuous
    { toFun := fun z => c • z
      map_add' := by intro x y; exact smul_add c x y
      map_smul' := by intro a x; simp [smul_smul, mul_comm] }
    |c| (by intro z; simp [norm_smul, Real.norm_eq_abs])
  have hphysLaw := fs4PhysicalFiniteMarginal_hasGaussianLaw L mass hL hmass js hjs
  have hphys : IsGaussian (fs4PhysicalFiniteMarginal L mass js) := by
    simpa using hphysLaw.isGaussian_map
  letI : IsGaussian (Measure.map S (fs4PhysicalFiniteMarginal L mass js)) :=
    isGaussian_map_of_measurable S.continuous.measurable
  have hmap : Measure.map S (fs4PhysicalFiniteMarginal L mass js) =
      Measure.map (fun z : E => c • z) (fs4PhysicalFiniteMarginal L mass js) := by
    congr 1
  rw [← hmap]
  simpa only [Measure.map_id, id_eq] using
    (show IsGaussian (Measure.map S (fs4PhysicalFiniteMarginal L mass js)) from inferInstance).hasGaussianLaw_id

theorem periodic3DGaussianTargetMeasure_canonicalProjection_mean
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0))
    (t : EuclideanSpace ℝ (Fin m)) :
    ∫ z, inner ℝ t z ∂((periodic3DGaussianTargetMeasure L mass).map
      (periodic3DCanonicalCoordinateProjection js)) = 0 := by
  rw [periodic3DGaussianTargetMeasure_map_canonicalProjection L mass js hsupport]
  rw [integral_map (show AEMeasurable
    (fun z : EuclideanSpace ℝ (Fin m) => (Real.sqrt L)⁻¹ • z)
    (fs4PhysicalFiniteMarginal L mass js) from (by fun_prop)) (by fun_prop)]
  simp only [inner_smul_right]
  rw [integral_const_mul, fs4PhysicalFiniteMarginal_mean L mass hL hmass js t, mul_zero]

theorem periodic3DGaussianTargetMeasure_canonicalProjection_variance
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (hjs : Function.Injective js)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0))
    (t : EuclideanSpace ℝ (Fin m)) :
    Var[fun z => inner ℝ t z; (periodic3DGaussianTargetMeasure L mass).map
      (periodic3DCanonicalCoordinateProjection js)] =
      ((Real.sqrt L)⁻¹)^2 *
        ∑ i : Fin m, (t i * fs4PhysicalRealCoordinateScale L mass (js i))^2 := by
  rw [periodic3DGaussianTargetMeasure_map_canonicalProjection L mass js hsupport]
  rw [variance_map (by fun_prop) (show AEMeasurable
    (fun z : EuclideanSpace ℝ (Fin m) => (Real.sqrt L)⁻¹ • z)
    (fs4PhysicalFiniteMarginal L mass js) from (by fun_prop))]
  simp only [Function.comp_def, inner_smul_right]
  rw [variance_const_mul, fs4PhysicalFiniteMarginal_variance L mass hL hmass js hjs t]


/-- Gaussian identification from an explicit covariance matrix identity. The identity
is an input here, to be discharged for the concrete canonical tests separately. -/
theorem periodic3DCanonicalProjection_eq_resolventTarget_of_covariance
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (hjs : Function.Injective js)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0))
    (fs : Fin m → BoundedContinuousFunction (Fin 3 → ℝ) ℝ)
    (hcov : ∀ i j, periodicResolventCovarianceMatrix 3 m L mass hmass fs i j =
      if i = j then ((Real.sqrt L)⁻¹)^2 *
        (fs4PhysicalRealCoordinateScale L mass (js i))^2 else 0) :
    (periodic3DGaussianTargetMeasure L mass).map
      (periodic3DCanonicalCoordinateProjection js) =
      periodicResolventTargetMeasure 3 m L mass hmass fs := by
  classical
  have hv (t : EuclideanSpace ℝ (Fin m)) :
      (∑ i : Fin m, ∑ j : Fin m, t i * t j *
        periodicResolventCovarianceMatrix 3 m L mass hmass fs i j) =
      ((Real.sqrt L)⁻¹)^2 * ∑ i : Fin m,
        (t i * fs4PhysicalRealCoordinateScale L mass (js i))^2 := by
    simp_rw [hcov]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  letI : IsProbabilityMeasure (periodicResolventTargetMeasure 3 m L mass hmass fs) := by
    unfold periodicResolventTargetMeasure
    infer_instance
  letI : IsProbabilityMeasure ((periodic3DGaussianTargetMeasure L mass).map
      (periodic3DCanonicalCoordinateProjection js)) :=
    (Measure.isProbabilityMeasure_map_iff
      (continuous_periodic3DCanonicalCoordinateProjection js).measurable.aemeasurable).2 inferInstance
  apply Measure.ext_of_charFun
  funext t
  have hl := (periodic3DGaussianTargetMeasure_canonicalProjection_hasGaussianLaw
    L mass hL hmass js hjs hsupport).charFun_map_eq t
  have hr := (periodicResolventTargetMeasure_hasGaussianLaw 3 m L mass hmass fs).charFun_map_eq t
  simp only [Measure.map_id, id_eq] at hl hr
  rw [hl, hr, periodic3DGaussianTargetMeasure_canonicalProjection_mean L mass hL hmass js hsupport t,
    periodicResolventTargetMeasure_mean_zero 3 m L mass hmass,
    periodic3DGaussianTargetMeasure_canonicalProjection_variance L mass hL hmass js hjs hsupport t,
    periodicResolventTargetMeasure_covariance_quadratic 3 m L mass hL hmass, hv t]


def periodic3DCanonicalPairVariance (L mass : ℝ) (k : Periodic3DIndex) : ℝ :=
  L ^ 3 / (2 * torusMassSymbol 3 L mass k)

theorem periodic3D_fourthZeroCanonicalScale_variance
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k : FS4CanonicalPairIndex) (hk0 : k.1 3 = 0) (useSine : Bool) :
    (fs4PhysicalRealCoordinateScale L mass (Sum.inr (k,useSine))) ^ 2 / L =
      periodic3DCanonicalPairVariance L mass (periodic3DRestrictIndex k.1) := by
  have hext := periodic3DExtend_restrictIndex_of_fourth_zero k.1 hk0
  have hs : torusMassSymbol 4 L mass k.1 =
      torusMassSymbol 3 L mass (periodic3DRestrictIndex k.1) := by
    rw [← hext]
    exact periodic3DExtend_massSymbol L mass (periodic3DRestrictIndex k.1)
  have hv := fs4GaussianRealPairScale_variance L mass k.1 hmass
  change (fs4GaussianRealPairScale L mass k.1) ^ 2 / L = _
  rw [periodic3DCanonicalPairVariance]
  rw [← hs]
  have hsym : 0 < torusMassSymbol 4 L mass k.1 := torusMassSymbol_pos 4 L mass hmass k.1
  dsimp [fs4PhysicalRealCoordinateScale, fs4GaussianRealPairScale] at hv ⊢
  field_simp [hL.ne', hsym.ne', Real.sqrt_ne_zero'.mpr (show 0 < (2:ℝ) by norm_num)] at hv ⊢
  nlinarith [hv]


def periodic3DFirstNonzeroPositive (k : Periodic3DIndex) : Prop :=
  ∃ j : Fin 3, (∀ i, i < j → k i = 0) ∧ 0 < k j

theorem periodic3DExtend_firstNonzeroPositive_iff (k : Periodic3DIndex) :
    fs4FirstNonzeroPositive (periodic3DExtend k) ↔ periodic3DFirstNonzeroPositive k := by
  constructor
  · rintro ⟨j, hj, hpos⟩
    have hj3 : j.val < 3 := by
      by_contra h
      have : periodic3DExtend k j = 0 := by simp [periodic3DExtend, h]
      omega
    refine ⟨⟨j.val, hj3⟩, ?_, ?_⟩
    · intro i hij
      have hi : (⟨i.val, by omega⟩ : Fin 4) < j := by exact_mod_cast hij
      have hz := hj _ hi
      have hi_lt : i.val < 3 := by omega
      simpa [periodic3DExtend, hi_lt] using hz
    · have hjval : j.val < 3 := by omega
      simpa [periodic3DExtend, hjval] using hpos
  · rintro ⟨j, hj, hpos⟩
    refine ⟨Fin.castSucc j, ?_, ?_⟩
    · intro i hij
      have hiv : i.val < j.val := by exact_mod_cast hij
      have hi : (⟨i.val, by omega⟩ : Fin 3) < j := by exact hiv
      have hz := hj _ hi
      have hi_lt : i.val < 3 := by omega
      simpa [periodic3DExtend, hi_lt] using hz
    · have hj3 : j.val < 3 := j.isLt
      simpa [periodic3DExtend, hj3] using hpos

def Periodic3DCanonicalPairIndex := {k : Periodic3DIndex // k ≠ 0 ∧ periodic3DFirstNonzeroPositive k}

def periodic3DCanonicalPairEmbed (k : Periodic3DCanonicalPairIndex) : FS4CanonicalPairIndex :=
  ⟨periodic3DExtend k.1, ⟨fun h => k.2.1 (by
      have hz0 : periodic3DExtend (0 : Periodic3DIndex) = (0 : FS4Index) := by ext i; fin_cases i <;> simp [periodic3DExtend]
      apply periodic3DExtend_injective
      rw [hz0]
      exact h),
    (periodic3DExtend_firstNonzeroPositive_iff k.1).2 k.2.2⟩⟩


def periodic3DCanonicalPairRestrict (k : FS4CanonicalPairIndex) (hk0 : k.1 3 = 0) :
    Periodic3DCanonicalPairIndex := by
  refine ⟨periodic3DRestrictIndex k.1, ?_, ?_⟩
  · intro hz
    have hext := periodic3DExtend_restrictIndex_of_fourth_zero k.1 hk0
    apply k.2.1
    rw [← hext, hz]
    have hzero : periodic3DExtend (0 : Periodic3DIndex) = (0 : FS4Index) := by
      ext i
      fin_cases i <;> simp [periodic3DExtend]
    exact hzero
  · have hcan : fs4FirstNonzeroPositive (periodic3DExtend (periodic3DRestrictIndex k.1)) := by
      simpa only [periodic3DExtend_restrictIndex_of_fourth_zero k.1 hk0] using k.2.2
    exact (periodic3DExtend_firstNonzeroPositive_iff _).1 hcan

theorem periodic3DCanonicalPairEmbed_restrict (k : FS4CanonicalPairIndex) (hk0 : k.1 3 = 0) :
    periodic3DCanonicalPairEmbed (periodic3DCanonicalPairRestrict k hk0) = k := by
  apply Subtype.ext
  exact periodic3DExtend_restrictIndex_of_fourth_zero k.1 hk0

theorem periodic3DCanonicalPairRestrict_embed (k : Periodic3DCanonicalPairIndex) :
    periodic3DCanonicalPairRestrict (periodic3DCanonicalPairEmbed k) (by
      change periodic3DExtend k.1 3 = 0
      simp [periodic3DExtend]) = k := by
  apply Subtype.ext
  change periodic3DRestrictIndex (periodic3DExtend k.1) = k.1
  funext i
  simp [periodic3DRestrictIndex, periodic3DExtend]


end Pphi2Clean.Continuum
