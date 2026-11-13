import AImathPPhi2Clean.Periodic3DHminusThreeInclusion

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

theorem periodic3DFixedVolumeH3_map_inclusion
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    (periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass n).map periodic3DH3ToH4 =
      periodic3DFixedVolumeProbabilityMeasure L mass hL hmass n := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map periodic3DH3ToH4
    (Measure.map (periodic3DFiniteSourceFourierLiftH3 (n+1) (L / ((n+1 : ℕ) : ℝ)) L) _) = _
  rw [Measure.map_map (show Measurable periodic3DH3ToH4 from periodic3DH3ToH4CLM.continuous.measurable)
    (measurable_periodic3DFiniteSourceFourierLiftH3 _ _ _)]
  change Measure.map _ _ = Measure.map (periodic3DFiniteSourceFourierLift (n+1) (L / ((n+1 : ℕ) : ℝ)) L) _
  congr 1
  funext ω
  exact periodic3DH3ToH4_finiteSource _ _ _ ω

theorem periodic3DH3ToH4_probability_map_injective :
    Function.Injective (fun μ : ProbabilityMeasure Periodic3DCompletion => μ.map periodic3DH3ToH4) := by
  letI : TopologicalSpace.SeparableSpace Periodic3DCompletion := periodic3DHminusFourCompletion_separable
  have he : MeasurableEmbedding periodic3DH3ToH4 :=
    periodic3DH3ToH4CLM.continuous.measurableEmbedding periodic3DH3ToH4_injective
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply he.map_injective
  exact congrArg (fun ρ : ProbabilityMeasure Periodic3DCompletion => (ρ : Measure Periodic3DCompletion)) h

 theorem periodic3DFixedVolumeH3_subsequential_limit_map
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (ν : ProbabilityMeasure Periodic3DCompletion)
    (hν : Tendsto (fun k => periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass (ns k)) atTop (𝓝 ν)) :
    ν.map periodic3DH3ToH4 = periodic3DGaussianTargetProbabilityMeasure L mass := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
    (show Continuous periodic3DH3ToH4 from periodic3DH3ToH4CLM.continuous)
  have hmap' : Tendsto (fun k =>
      (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass (ns k))) atTop
      (𝓝 (ν.map periodic3DH3ToH4)) := by
    simpa only [periodic3DFixedVolumeH3_map_inclusion] using hmap
  exact tendsto_nhds_unique hmap'
    ((periodic3DFixedVolume_weak_tendsto_gaussianTarget L mass hL hmass).comp hns)

theorem periodic3DFixedVolumeH3_subsequential_limits_eq
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (μ ν : ProbabilityMeasure Periodic3DCompletion) (ns ms : ℕ → ℕ)
    (hns : Tendsto ns atTop atTop) (hms : Tendsto ms atTop atTop)
    (hμ : Tendsto (fun k => periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass (ns k)) atTop (𝓝 μ))
    (hν : Tendsto (fun k => periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass (ms k)) atTop (𝓝 ν)) : μ = ν := by
  apply periodic3DH3ToH4_probability_map_injective
  change μ.map periodic3DH3ToH4 = ν.map periodic3DH3ToH4
  rw [periodic3DFixedVolumeH3_subsequential_limit_map L mass hL hmass ns hns μ hμ,
    periodic3DFixedVolumeH3_subsequential_limit_map L mass hL hmass ms hms ν hν]

theorem periodic3DFixedVolumeH3_weak_limit_exists
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ μ : ProbabilityMeasure Periodic3DCompletion,
      Tendsto (periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass) atTop (𝓝 μ) := by
  obtain ⟨ms0, μ, hms0, hμ⟩ := periodic3DFixedVolumeH3_prokhorov_subsequence L mass hL hmass id tendsto_id
  refine ⟨μ, ?_⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, ν, hms, hν⟩ := periodic3DFixedVolumeH3_prokhorov_subsequence L mass hL hmass ns hns
  have heq : ν = μ := periodic3DFixedVolumeH3_subsequential_limits_eq L mass hL hmass ν μ
    (fun k => ns (ms k)) ms0 (hns.comp hms.tendsto_atTop) hms0.tendsto_atTop hν hμ
  exact ⟨ms, heq ▸ hν⟩

def periodic3DGaussianTargetProbabilityMeasureH3 (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ProbabilityMeasure Periodic3DCompletion :=
  (periodic3DFixedVolumeH3_weak_limit_exists L mass hL hmass).choose

theorem periodic3DFixedVolumeH3_weak_tendsto_gaussianTarget
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Tendsto (periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass) atTop
      (𝓝 (periodic3DGaussianTargetProbabilityMeasureH3 L mass hL hmass)) :=
  (periodic3DFixedVolumeH3_weak_limit_exists L mass hL hmass).choose_spec

theorem periodic3DGaussianTargetH3_map_inclusion
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    (periodic3DGaussianTargetProbabilityMeasureH3 L mass hL hmass).map periodic3DH3ToH4 =
      periodic3DGaussianTargetProbabilityMeasure L mass := by
  exact periodic3DFixedVolumeH3_subsequential_limit_map L mass hL hmass id tendsto_id _
    (periodic3DFixedVolumeH3_weak_tendsto_gaussianTarget L mass hL hmass)

theorem periodic3DFixedVolumeH3_weak_limit_existsUnique
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃! μ : ProbabilityMeasure Periodic3DCompletion,
      Tendsto (periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ⟩ := periodic3DFixedVolumeH3_weak_limit_exists L mass hL hmass
  exact ⟨μ, hμ, fun ν hν => tendsto_nhds_unique hν hμ⟩

end Pphi2Clean.Continuum
