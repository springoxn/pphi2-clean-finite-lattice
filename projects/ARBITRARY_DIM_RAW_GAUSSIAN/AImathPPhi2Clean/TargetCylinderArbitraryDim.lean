import AImathPPhi2Clean.ArbitraryDimParameters
import AImathPPhi2Clean.TargetTruncationArbitraryDim
import Mathlib.MeasureTheory.Constructions.Cylinders

set_option maxRecDepth 500000
set_option maxHeartbeats 0
noncomputable section
namespace Pphi2Clean.ArbitraryDimGaussian
open Pphi2Clean.ArbitraryDim
variable [Parameters]
open MeasureTheory ProbabilityTheory Topology Filter

def targetCoordinateEmbedding (x : TargetCompletion) : Index → ℂ := fun k => x k

theorem continuous_targetCoordinateEmbedding : Continuous targetCoordinateEmbedding := by
  apply continuous_pi
  intro k
  exact (lp.evalCLM ℂ (fun _ : Index => ℂ) 2 k).continuous

theorem injective_targetCoordinateEmbedding : Function.Injective targetCoordinateEmbedding := by
  intro x y h
  apply lp.ext
  funext k
  exact congrFun h k

theorem measurableEmbedding_targetCoordinateEmbedding :
    MeasurableEmbedding targetCoordinateEmbedding :=
  continuous_targetCoordinateEmbedding.measurableEmbedding injective_targetCoordinateEmbedding

def targetFiniteCoordinates (s : Finset Index) (x : TargetCompletion) : s → ℂ :=
  s.restrict (targetCoordinateEmbedding x)

theorem continuous_targetFiniteCoordinates (s : Finset Index) :
    Continuous (targetFiniteCoordinates s) := by
  apply continuous_pi
  intro k
  exact (lp.evalCLM ℂ (fun _ : Index => ℂ) 2 k).continuous

def targetMeasurableCylinders : Set (Set TargetCompletion) :=
  {A | ∃ t ∈ measurableCylinders (fun _ : Index => ℂ), targetCoordinateEmbedding ⁻¹' t = A}

theorem target_cylinder_sigma_eq_borel :
    MeasurableSpace.generateFrom targetMeasurableCylinders = borel TargetCompletion := by
  have hc : MeasurableSpace.generateFrom targetMeasurableCylinders =
      MeasurableSpace.comap targetCoordinateEmbedding
        (MeasurableSpace.pi : MeasurableSpace (Index → ℂ)) := by
    rw [← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
    rfl
  rw [hc, measurableEmbedding_targetCoordinateEmbedding.comap_eq]
  rfl

theorem target_measure_ext_of_finite_marginals
    (μ ν : Measure TargetCompletion) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ s : Finset Index, Measure.map (targetFiniteCoordinates s) μ =
      Measure.map (targetFiniteCoordinates s) ν)
    (huniv : μ Set.univ = ν Set.univ) : μ = ν := by
  apply ext_of_generate_finite targetMeasurableCylinders target_cylinder_sigma_eq_borel.symm
    (isPiSystem_measurableCylinders.comap targetCoordinateEmbedding)
  · rintro A ⟨t, ht, rfl⟩
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht
    have hh := congrArg (fun ρ : Measure (s → ℂ) => ρ S) (h s)
    change μ (targetFiniteCoordinates s ⁻¹' S) = ν (targetFiniteCoordinates s ⁻¹' S)
    simpa only [Measure.map_apply (continuous_targetFiniteCoordinates s).measurable hS] using hh
  · exact huniv

theorem target_probabilityMeasure_ext_of_finite_marginals
    (μ ν : ProbabilityMeasure TargetCompletion)
    (h : ∀ s : Finset Index, μ.map (targetFiniteCoordinates s) =
      ν.map (targetFiniteCoordinates s)) : μ = ν := by
  apply Subtype.ext
  apply target_measure_ext_of_finite_marginals (μ : Measure TargetCompletion)
    (ν : Measure TargetCompletion)
  · intro s
    exact congrArg (fun ρ : ProbabilityMeasure (s → ℂ) => (ρ : Measure (s → ℂ))) (h s)
  · simp

/-- Uniqueness of target weak limits follows from uniqueness of every finite-coordinate limit. -/
theorem target_weak_limits_eq_of_finite_marginals
    (μ : ℕ → ProbabilityMeasure TargetCompletion)
    (ν₁ ν₂ : ProbabilityMeasure TargetCompletion)
    (n₁ n₂ : ℕ → ℕ)
    (h₁ : Tendsto (fun k => μ (n₁ k)) atTop (𝓝 ν₁))
    (h₂ : Tendsto (fun k => μ (n₂ k)) atTop (𝓝 ν₂))
    (hmarg : ∀ s : Finset Index, ∃ ρ : ProbabilityMeasure (s → ℂ),
      Tendsto (fun k => (μ (n₁ k)).map (targetFiniteCoordinates s))
        atTop (𝓝 ρ) ∧
      Tendsto (fun k => (μ (n₂ k)).map (targetFiniteCoordinates s))
        atTop (𝓝 ρ)) : ν₁ = ν₂ := by
  apply target_probabilityMeasure_ext_of_finite_marginals
  intro s
  obtain ⟨ρ, hρ₁, hρ₂⟩ := hmarg s
  have hc := ProbabilityMeasure.continuous_map (continuous_targetFiniteCoordinates s)
  have he₁ := tendsto_nhds_unique (hc.continuousAt.tendsto.comp h₁) hρ₁
  have he₂ := tendsto_nhds_unique (hc.continuousAt.tendsto.comp h₂) hρ₂
  exact he₁.trans he₂.symm

/-- Tightness and Borel uniqueness reduce the remaining fixed-volume problem to
convergence of the actual finite-coordinate laws. This theorem does not supply
that analytic hypothesis. -/
theorem actualTarget_fixedVolume_exists_weak_limit_of_finite_marginal_limits
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (hmarg : ∀ s : Finset Index, ∃ ρ : ProbabilityMeasure (s → ℂ),
      Tendsto (fun n => (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass n).map
        (targetFiniteCoordinates s)) atTop (𝓝 ρ)) :
    ∃ ν : ProbabilityMeasure TargetCompletion,
      Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop (𝓝 ν) := by
  let μ := actualTargetProbabilityMeasure_fixedVolume L mass hL hmass
  obtain ⟨ms₀, ν₀, hms₀, hν₀⟩ :=
    actualTargetProbabilityMeasure_fixedVolume_prokhorov_subsequence L mass hL hmass id
  refine ⟨ν₀, ?_⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, ν, hms, hν⟩ :=
    actualTargetProbabilityMeasure_fixedVolume_prokhorov_subsequence L mass hL hmass ns
  have heq : ν = ν₀ := by
    apply target_weak_limits_eq_of_finite_marginals μ ν ν₀
      (fun k => ns (ms k)) ms₀ hν hν₀
    intro s
    obtain ⟨ρ, hρ⟩ := hmarg s
    exact ⟨ρ, hρ.comp (hns.comp hms.tendsto_atTop), hρ.comp hms₀.tendsto_atTop⟩
  exact ⟨ms, by simpa [heq] using hν⟩

#print axioms actualTarget_fixedVolume_exists_weak_limit_of_finite_marginal_limits
#print axioms target_cylinder_sigma_eq_borel
#print axioms target_probabilityMeasure_ext_of_finite_marginals
#print axioms target_weak_limits_eq_of_finite_marginals
end Pphi2Clean.ArbitraryDimGaussian
