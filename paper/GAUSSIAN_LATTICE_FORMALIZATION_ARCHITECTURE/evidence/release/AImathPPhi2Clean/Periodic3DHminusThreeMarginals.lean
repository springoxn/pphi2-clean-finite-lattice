import AImathPPhi2Clean.Periodic3DHminusThreeWeakLimit

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

/-- Physical real/sine coordinates of H⁻³ weighted Fourier data. -/
def periodic3DFourierFamilyProjectionH3 {m : ℕ} (L : ℝ) (hL : 0 < L)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :=
  periodic3DFourierFamilyProjection L hL modes useSine ∘ periodic3DH3ToH4

theorem continuous_periodic3DFourierFamilyProjectionH3 {m : ℕ} (L : ℝ) (hL : 0 < L)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    Continuous (periodic3DFourierFamilyProjectionH3 L hL modes useSine) :=
  (continuous_periodic3DFourierFamilyProjection L hL modes useSine).comp
    periodic3DH3ToH4CLM.continuous

theorem periodic3DGaussianTargetH3_fourierFamily_law
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    (periodic3DGaussianTargetProbabilityMeasureH3 L mass hL hmass).map
      (periodic3DFourierFamilyProjectionH3 L hL modes useSine) =
      periodicResolventTargetProbabilityMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine) := by
  have hmap : (periodic3DGaussianTargetProbabilityMeasureH3 L mass hL hmass).map
      (periodic3DFourierFamilyProjectionH3 L hL modes useSine) =
      ((periodic3DGaussianTargetProbabilityMeasureH3 L mass hL hmass).map periodic3DH3ToH4).map
        (periodic3DFourierFamilyProjection L hL modes useSine) := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, periodic3DFourierFamilyProjectionH3]
    exact (Measure.map_map
      (continuous_periodic3DFourierFamilyProjection L hL modes useSine).measurable
      (show Measurable periodic3DH3ToH4 from periodic3DH3ToH4CLM.continuous.measurable)).symm
  rw [hmap, periodic3DGaussianTargetH3_map_inclusion]
  exact periodic3DFixedVolume_weak_limit_fourierFamily m L mass hL hmass modes useSine _
    (periodic3DFixedVolume_weak_tendsto_gaussianTarget L mass hL hmass)

theorem periodic3DFixedVolumeH3_fourierFamilyMarginal_tendsto
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    Tendsto (fun n => (periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass n).map
      (periodic3DFourierFamilyProjectionH3 L hL modes useSine)) atTop
      (𝓝 (periodicResolventTargetProbabilityMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine))) := by
  rw [← periodic3DGaussianTargetH3_fourierFamily_law L mass hL hmass modes useSine]
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (periodic3DFixedVolumeH3_weak_tendsto_gaussianTarget L mass hL hmass)
    (continuous_periodic3DFourierFamilyProjectionH3 L hL modes useSine)

/-- The target is characterized independently of the choice of subsequence. -/
theorem periodic3DGaussianTargetH3_unique_lift
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ν : ProbabilityMeasure Periodic3DCompletion)
    (hν : ν.map periodic3DH3ToH4 = periodic3DGaussianTargetProbabilityMeasure L mass) :
    ν = periodic3DGaussianTargetProbabilityMeasureH3 L mass hL hmass := by
  apply periodic3DH3ToH4_probability_map_injective
  change ν.map periodic3DH3ToH4 = (periodic3DGaussianTargetProbabilityMeasureH3 L mass hL hmass).map periodic3DH3ToH4
  rw [hν, periodic3DGaussianTargetH3_map_inclusion]

theorem periodic3DH3_probability_ext_of_fourierFamily_marginals
    (L : ℝ) (hL : 0 < L) (μ ν : ProbabilityMeasure Periodic3DCompletion)
    (hmarg : ∀ (m : ℕ) (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool),
      μ.map (periodic3DFourierFamilyProjectionH3 L hL modes useSine) =
      ν.map (periodic3DFourierFamilyProjectionH3 L hL modes useSine)) : μ = ν := by
  apply periodic3DH3ToH4_probability_map_injective
  apply periodic3D_probabilityMeasure_ext_of_fourierFamily_marginals L hL
  intro m modes useSine
  have hcomp (ρ : ProbabilityMeasure Periodic3DCompletion) :
      (ρ.map periodic3DH3ToH4).map (periodic3DFourierFamilyProjection L hL modes useSine) =
        ρ.map (periodic3DFourierFamilyProjectionH3 L hL modes useSine) := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, periodic3DFourierFamilyProjectionH3]
    exact Measure.map_map
      (continuous_periodic3DFourierFamilyProjection L hL modes useSine).measurable
      (show Measurable periodic3DH3ToH4 from periodic3DH3ToH4CLM.continuous.measurable)
  rw [hcomp, hcomp, hmarg]

end Pphi2Clean.Continuum
