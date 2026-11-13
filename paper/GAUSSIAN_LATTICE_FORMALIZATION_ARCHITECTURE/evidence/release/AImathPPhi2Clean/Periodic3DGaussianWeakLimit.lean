import AImathPPhi2Clean.Periodic3DCanonicalMarginal
import AImathPPhi2Clean.Periodic3DRealCarrier
import AImathPPhi2Clean.Periodic3DWeakLimitExistence

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

abbrev Periodic3DSupportedRealCoordinateIndex :=
  {j : FS4GaussianRealCoordinateIndex // j.elim (fun _ => True) (fun q => q.1.1 3 = 0)}

def periodic3DPhysicalCoordinateEncoding (x : Periodic3DCompletion) :
    Periodic3DSupportedRealCoordinateIndex → ℝ := fun j =>
  (periodic3DCanonicalCoordinateProjection (fun _ : Fin 1 => j.1) x) 0

theorem periodic3DPhysicalCoordinateEncoding_continuous :
    Continuous periodic3DPhysicalCoordinateEncoding := by
  apply continuous_pi
  intro j
  exact ((continuous_apply 0).comp (PiLp.continuous_ofLp 2 _)).comp
    (continuous_periodic3DCanonicalCoordinateProjection (fun _ : Fin 1 => j.1))

theorem periodic3DPhysicalCoordinateEncoding_injOn :
    Set.InjOn periodic3DPhysicalCoordinateEncoding periodic3DHminusFourRealCarrier := by
  intro x hx y hy heq
  have h (j : Periodic3DSupportedRealCoordinateIndex) := congrFun heq j
  have hrestrict (k : Periodic3DIndex) :
      periodic3DRestrictIndex (periodic3DExtend k) = k := by
    funext i
    simp [periodic3DRestrictIndex, periodic3DExtend]
  have hcanonical (k : Periodic3DCanonicalPairIndex) : x k.1 = y k.1 := by
    let p := periodic3DCanonicalPairEmbed k
    have hp : p.1 3 = 0 := by simp [p, periodic3DCanonicalPairEmbed, periodic3DExtend]
    have hr := h ⟨Sum.inr (p, false), hp⟩
    have hi := h ⟨Sum.inr (p, true), hp⟩
    change (x (periodic3DRestrictIndex p.1) / (Real.sqrt
      (periodic3DHminusFourWeight (periodic3DRestrictIndex p.1)) : ℂ)).re =
      (y (periodic3DRestrictIndex p.1) / (Real.sqrt
      (periodic3DHminusFourWeight (periodic3DRestrictIndex p.1)) : ℂ)).re at hr
    change (x (periodic3DRestrictIndex p.1) / (Real.sqrt
      (periodic3DHminusFourWeight (periodic3DRestrictIndex p.1)) : ℂ)).im =
      (y (periodic3DRestrictIndex p.1) / (Real.sqrt
      (periodic3DHminusFourWeight (periodic3DRestrictIndex p.1)) : ℂ)).im at hi
    have hpval : periodic3DRestrictIndex p.1 = k.1 := hrestrict k.1
    rw [hpval] at hr hi
    have hroot : (Real.sqrt (periodic3DHminusFourWeight k.1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 4 (periodic3DExtend k.1))).ne'
    exact (div_left_inj' hroot).mp (Complex.ext hr hi)
  have hz : x 0 = y 0 := by
    have hr := h ⟨Sum.inl (), trivial⟩
    change (x 0).re = (y 0).re at hr
    have hxi := congrArg Complex.im (hx 0)
    have hyi := congrArg Complex.im (hy 0)
    change (x 0).im = -(x 0).im at hxi
    change (y 0).im = -(y 0).im at hyi
    apply Complex.ext hr
    linarith
  apply lp.ext
  funext k
  by_cases hk : k = 0
  · simpa [hk] using hz
  · have hext : periodic3DExtend k ≠ 0 := by
      intro he
      apply hk
      have hh := congrArg periodic3DRestrictIndex he
      rw [hrestrict] at hh
      exact hh.trans (by rfl)
    rcases fs4FirstNonzeroPositive_or_neg (periodic3DExtend k) hext with hpos | hneg
    · exact hcanonical ⟨k, hk, (periodic3DExtend_firstNonzeroPositive_iff k).1 hpos⟩
    · have hnpos : periodic3DFirstNonzeroPositive (-k) := by
        apply (periodic3DExtend_firstNonzeroPositive_iff (-k)).1
        rw [periodic3DExtend_neg]
        exact hneg
      have hxy := hcanonical ⟨-k, neg_ne_zero.mpr hk, hnpos⟩
      change x (-k) = y (-k) at hxy
      rw [hx k, hy k] at hxy
      exact star_injective hxy

theorem periodic3DHminusFour_measure_ext_of_real_encoding (μ ν : Measure Periodic3DCompletion)
    (hμ : ∀ᵐ x ∂μ, x ∈ periodic3DHminusFourRealCarrier)
    (hν : ∀ᵐ x ∂ν, x ∈ periodic3DHminusFourRealCarrier)
    (hmap : Measure.map periodic3DPhysicalCoordinateEncoding μ = Measure.map periodic3DPhysicalCoordinateEncoding ν) : μ = ν := by
  letI : TopologicalSpace.SeparableSpace Periodic3DCompletion := periodic3DHminusFourCompletion_separable
  apply Measure.ext
  intro A hA
  let B := periodic3DPhysicalCoordinateEncoding '' (A ∩ periodic3DHminusFourRealCarrier)
  have hB : MeasurableSet B :=
    (hA.inter periodic3DHminusFourRealCarrier_closed.measurableSet).image_of_continuousOn_injOn
      periodic3DPhysicalCoordinateEncoding_continuous.continuousOn
      (periodic3DPhysicalCoordinateEncoding_injOn.mono Set.inter_subset_right)
  have heq (x : Periodic3DCompletion) (hx : x ∈ periodic3DHminusFourRealCarrier) :
      x ∈ A ↔ x ∈ periodic3DPhysicalCoordinateEncoding ⁻¹' B := by
    constructor
    · intro ha
      exact ⟨x,⟨ha,hx⟩,rfl⟩
    · rintro ⟨y,⟨hy,hyR⟩,hxy⟩
      have hyx := periodic3DPhysicalCoordinateEncoding_injOn hyR hx hxy
      simpa only [hyx] using hy
  have hμeq : μ A = μ (periodic3DPhysicalCoordinateEncoding ⁻¹' B) := by
    apply measure_congr
    filter_upwards [hμ] with x hx
    exact propext (heq x hx)
  have hνeq : ν A = ν (periodic3DPhysicalCoordinateEncoding ⁻¹' B) := by
    apply measure_congr
    filter_upwards [hν] with x hx
    exact propext (heq x hx)
  rw [hμeq, hνeq, ← Measure.map_apply periodic3DPhysicalCoordinateEncoding_continuous.measurable hB,
    ← Measure.map_apply periodic3DPhysicalCoordinateEncoding_continuous.measurable hB, hmap]


theorem periodic3DHminusFour_probabilityMeasure_ext_of_supported_finite_marginals
    (μ ν : ProbabilityMeasure Periodic3DCompletion)
    (hμ : ∀ᵐ x ∂(μ : Measure Periodic3DCompletion), x ∈ periodic3DHminusFourRealCarrier)
    (hν : ∀ᵐ x ∂(ν : Measure Periodic3DCompletion), x ∈ periodic3DHminusFourRealCarrier)
    (hmarg : ∀ (m : ℕ) (js : Fin m → Periodic3DSupportedRealCoordinateIndex), Function.Injective js →
      μ.map (periodic3DCanonicalCoordinateProjection (fun i => (js i).1)) = ν.map (periodic3DCanonicalCoordinateProjection (fun i => (js i).1))) : μ = ν := by
  classical
  apply ProbabilityMeasure.toMeasure_injective
  apply periodic3DHminusFour_measure_ext_of_real_encoding _ _ hμ hν
  let f := periodic3DPhysicalCoordinateEncoding
  have hf : Measurable f := periodic3DPhysicalCoordinateEncoding_continuous.measurable
  letI : IsProbabilityMeasure (Measure.map f (μ : Measure Periodic3DCompletion)) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (Measure.map f (ν : Measure Periodic3DCompletion)) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  apply ext_of_generate_finite (measurableCylinders (fun _ : Periodic3DSupportedRealCoordinateIndex => ℝ))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro A hA
    obtain ⟨s,S,hS,rfl⟩ := (mem_measurableCylinders A).mp hA
    let e : Fin s.card ≃ s := by simpa using (Fintype.equivFin s).symm
    let js : Fin s.card → Periodic3DSupportedRealCoordinateIndex := fun i => (e i).val
    have hjs : Function.Injective js := Subtype.val_injective.comp e.injective
    let g : EuclideanSpace ℝ (Fin s.card) → (∀ i : s, ℝ) := fun z i => z (e.symm i)
    have hg : Measurable g := by
      apply measurable_pi_lambda
      intro i
      exact ((continuous_apply _).comp (PiLp.continuous_ofLp 2 _)).measurable
    have hproj : (fun x : Periodic3DCompletion => s.restrict (f x)) = g ∘ periodic3DCanonicalCoordinateProjection (fun i => (js i).1) := by
      funext x i
      change periodic3DPhysicalCoordinateEncoding x i.val = periodic3DPhysicalCoordinateEncoding x (e (e.symm i)).val
      rw [e.apply_symm_apply]
    have hmap := congrArg (fun ρ : ProbabilityMeasure (EuclideanSpace ℝ (Fin s.card)) =>
      (ρ : Measure (EuclideanSpace ℝ (Fin s.card)))) (hmarg s.card js hjs)
    simp only [ProbabilityMeasure.toMeasure_map] at hmap
    have hmapg := congrArg (Measure.map g) hmap
    rw [Measure.map_map hg (continuous_periodic3DCanonicalCoordinateProjection (fun i => (js i).1)).measurable,
      Measure.map_map hg (continuous_periodic3DCanonicalCoordinateProjection (fun i => (js i).1)).measurable, ← hproj] at hmapg
    have hv := congrArg (fun ρ : Measure (∀ i : s, ℝ) => ρ S) hmapg
    change (Measure.map (s.restrict ∘ f) (μ : Measure _) ) S = (Measure.map (s.restrict ∘ f) (ν : Measure _)) S at hv
    rw [Measure.map_apply ((Finset.measurable_restrict s).comp hf) hS,
      Measure.map_apply ((Finset.measurable_restrict s).comp hf) hS] at hv
    rw [Measure.map_apply periodic3DPhysicalCoordinateEncoding_continuous.measurable (hS.cylinder s),
      Measure.map_apply periodic3DPhysicalCoordinateEncoding_continuous.measurable (hS.cylinder s)]
    exact hv
  · simp


theorem periodic3DHminusFour_probabilityMeasure_ext_of_real_finite_marginals
    (μ ν : ProbabilityMeasure Periodic3DCompletion)
    (hμ : ∀ᵐ x ∂(μ : Measure Periodic3DCompletion), x ∈ periodic3DHminusFourRealCarrier)
    (hν : ∀ᵐ x ∂(ν : Measure Periodic3DCompletion), x ∈ periodic3DHminusFourRealCarrier)
    (hmarg : ∀ (m : ℕ) (js : Fin m → FS4GaussianRealCoordinateIndex),
      Function.Injective js →
      (∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0)) →
      μ.map (periodic3DCanonicalCoordinateProjection js) =
      ν.map (periodic3DCanonicalCoordinateProjection js)) : μ = ν := by
  apply periodic3DHminusFour_probabilityMeasure_ext_of_supported_finite_marginals μ ν hμ hν
  intro m js hjs
  exact hmarg m (fun i => (js i).1) (Subtype.val_injective.comp hjs) (fun i => (js i).2)

theorem periodic3DFixedVolume_subsequential_limit_eq_gaussianTarget
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (ν : ProbabilityMeasure Periodic3DCompletion)
    (hν : Tendsto (fun n => periodic3DFixedVolumeProbabilityMeasure L mass hL hmass (ns n))
      atTop (𝓝 ν)) : ν = periodic3DGaussianTargetProbabilityMeasure L mass := by
  apply periodic3DHminusFour_probabilityMeasure_ext_of_real_finite_marginals
  · exact periodic3D_subsequence_limit_realCarrier_ae L mass hL hmass ns ν hν
  · exact periodic3DGaussianTargetMeasure_realCarrier_ae L mass hL hmass
  · intro m js hjs hsupport
    have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
      (continuous_periodic3DCanonicalCoordinateProjection js)
    exact tendsto_nhds_unique hmap
      ((periodic3DFixedVolume_canonicalMarginal_tendsto L mass hL hmass js hjs hsupport).comp hns)

theorem periodic3DFixedVolume_weak_limit_eq_gaussianTarget
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ν : ProbabilityMeasure Periodic3DCompletion)
    (hν : Tendsto (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass) atTop (𝓝 ν)) :
    ν = periodic3DGaussianTargetProbabilityMeasure L mass :=
  periodic3DFixedVolume_subsequential_limit_eq_gaussianTarget L mass hL hmass id tendsto_id ν hν

theorem periodic3DFixedVolume_weak_tendsto_gaussianTarget
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Tendsto (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass) atTop
      (𝓝 (periodic3DGaussianTargetProbabilityMeasure L mass)) := by
  obtain ⟨ν, hν⟩ := periodic3DFixedVolume_weak_limit_exists L mass hL hmass
  rw [← periodic3DFixedVolume_weak_limit_eq_gaussianTarget L mass hL hmass ν hν]
  exact hν

#print axioms periodic3DPhysicalCoordinateEncoding_injOn
#print axioms periodic3DHminusFour_probabilityMeasure_ext_of_real_finite_marginals
#print axioms periodic3DFixedVolume_subsequential_limit_eq_gaussianTarget
#print axioms periodic3DFixedVolume_weak_limit_eq_gaussianTarget
#print axioms periodic3DFixedVolume_weak_tendsto_gaussianTarget

end Pphi2Clean.Continuum
