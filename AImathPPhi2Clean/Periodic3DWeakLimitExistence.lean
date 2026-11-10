import AImathPPhi2Clean.Periodic3DAtomicMarginal
import AImathPPhi2Clean.Periodic3DCylinderUniqueness
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

/-- Joint real and imaginary Fourier families determine the complex cylinders. -/
theorem periodic3D_probabilityMeasure_ext_of_fourierFamily_marginals
    (L : ℝ) (hL : 0 < L) (μ ν : ProbabilityMeasure Periodic3DCompletion)
    (hmarg : ∀ (m : ℕ) (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool),
      μ.map (periodic3DFourierFamilyProjection L hL modes useSine) =
      ν.map (periodic3DFourierFamilyProjection L hL modes useSine)) : μ = ν := by
  apply periodic3DHminusFour_probabilityMeasure_ext_of_finite_marginals
  intro s
  let e : (s × Bool) ≃ Fin (Fintype.card (s × Bool)) := Fintype.equivFin _
  let modes : Fin (Fintype.card (s × Bool)) → Periodic3DIndex := fun j => (e.symm j).1.1
  let useSine : Fin (Fintype.card (s × Bool)) → Bool := fun j => (e.symm j).2
  let P := periodic3DFourierFamilyProjection L hL modes useSine
  let R : EuclideanSpace ℝ (Fin (Fintype.card (s × Bool))) → (∀ i : s, ℂ) :=
    fun y i => (Real.sqrt (periodic3DHminusFourWeight i.1) : ℂ) *
      ((y (e (i, false)) : ℂ) + (y (e (i, true)) : ℂ) * Complex.I)
  have hR : Measurable R := by
    have hcontinuous : Continuous R := by
      apply continuous_pi
      intro i
      dsimp [R]
      fun_prop
    exact hcontinuous.measurable
  have hP : Measurable P := (continuous_periodic3DFourierFamilyProjection L hL modes useSine).measurable
  have hfactor : R ∘ P = (fun x : Periodic3DCompletion => s.restrict (x : Periodic3DIndex → ℂ)) := by
    funext x i
    have hw : (Real.sqrt (periodic3DHminusFourWeight i.1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 4 (periodic3DExtend i.1))).ne'
    change (Real.sqrt (periodic3DHminusFourWeight i.1) : ℂ) *
      (((P x) (e (i, false)) : ℂ) + ((P x) (e (i, true)) : ℂ) * Complex.I) = x i.1
    simp only [P, periodic3DFourierFamilyProjection, modes, useSine, Equiv.symm_apply_apply, Bool.false_eq_true, ite_false, ite_true]
    rw [Complex.re_add_im]
    exact mul_div_cancel₀ _ hw
  have hmap (ρ : ProbabilityMeasure Periodic3DCompletion) :
      (ρ.map P).map R = ρ.map (fun x : Periodic3DCompletion => s.restrict (x : Periodic3DIndex → ℂ)) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact (Measure.map_map hR hP).trans (congrArg (fun f => Measure.map f (ρ : Measure _)) hfactor)
  rw [← hmap μ, ← hmap ν, hmarg _ modes useSine]

/-- Continuous mapping identifies every real Fourier-family marginal of a weak subsequential limit. -/
theorem periodic3DFixedVolume_subsequential_limit_fourierFamily
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool)
    (ν : ProbabilityMeasure Periodic3DCompletion) (ns : ℕ → ℕ)
    (hns : Tendsto ns atTop atTop)
    (hlim : Tendsto (fun k => periodic3DFixedVolumeProbabilityMeasure L mass hL hmass (ns k)) atTop (𝓝 ν)) :
    ν.map (periodic3DFourierFamilyProjection L hL modes useSine) =
      periodicResolventTargetProbabilityMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine) := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ hlim (continuous_periodic3DFourierFamilyProjection L hL modes useSine)
  exact tendsto_nhds_unique hmap
    ((periodic3DFixedVolume_fourierFamily_marginal_tendsto m L mass hL hmass modes useSine).comp hns)

/-- Every full weak limit has the Fourier marginals supplied by the actual finite-source convergence. -/
theorem periodic3DFixedVolume_weak_limit_fourierFamily
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool)
    (ν : ProbabilityMeasure Periodic3DCompletion)
    (hlim : Tendsto (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass) atTop (𝓝 ν)) :
    ν.map (periodic3DFourierFamilyProjection L hL modes useSine) =
      periodicResolventTargetProbabilityMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine) :=
  periodic3DFixedVolume_subsequential_limit_fourierFamily
    m L mass hL hmass modes useSine ν id tendsto_id hlim

/-- Any two weak subsequential limits of the actual atomic 3D laws coincide. -/
theorem periodic3DFixedVolume_subsequential_limits_eq
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (μ ν : ProbabilityMeasure Periodic3DCompletion) (ns ms : ℕ → ℕ)
    (hns : Tendsto ns atTop atTop) (hms : Tendsto ms atTop atTop)
    (hμ : Tendsto (fun k => periodic3DFixedVolumeProbabilityMeasure L mass hL hmass (ns k)) atTop (𝓝 μ))
    (hν : Tendsto (fun k => periodic3DFixedVolumeProbabilityMeasure L mass hL hmass (ms k)) atTop (𝓝 ν)) : μ = ν := by
  apply periodic3D_probabilityMeasure_ext_of_fourierFamily_marginals L hL μ ν
  intro m modes useSine
  rw [periodic3DFixedVolume_subsequential_limit_fourierFamily m L mass hL hmass modes useSine μ ns hns hμ,
    periodic3DFixedVolume_subsequential_limit_fourierFamily m L mass hL hmass modes useSine ν ms hms hν]

/-- Tightness and finite Fourier convergence give full weak convergence, without an assumed target. -/
theorem periodic3DFixedVolume_weak_limit_exists
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ μ : ProbabilityMeasure Periodic3DCompletion,
      Tendsto (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass) atTop (𝓝 μ) := by
  obtain ⟨ms0, μ, hms0, hμ⟩ := periodic3DFixedVolume_prokhorov_subsequence L mass hL hmass id tendsto_id
  refine ⟨μ, ?_⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, ν, hms, hν⟩ := periodic3DFixedVolume_prokhorov_subsequence L mass hL hmass ns hns
  have heq : ν = μ := periodic3DFixedVolume_subsequential_limits_eq L mass hL hmass ν μ
    (fun k => ns (ms k)) ms0 (hns.comp hms.tendsto_atTop) hms0.tendsto_atTop hν hμ
  exact ⟨ms, heq ▸ hν⟩

/-- Existence and uniqueness of the full weak limit of the actual 3D finite-source laws. -/
theorem periodic3DFixedVolume_weak_limit_existsUnique
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃! μ : ProbabilityMeasure Periodic3DCompletion,
      Tendsto (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ⟩ := periodic3DFixedVolume_weak_limit_exists L mass hL hmass
  exact ⟨μ, hμ, fun ν hν => tendsto_nhds_unique hν hμ⟩

#print axioms periodic3DFixedVolume_weak_limit_existsUnique
#print axioms periodic3DFixedVolume_subsequential_limits_eq
end Pphi2Clean.Continuum
