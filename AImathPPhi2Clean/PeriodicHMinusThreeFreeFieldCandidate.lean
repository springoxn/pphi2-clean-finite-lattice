import AImathPPhi2Clean.PeriodicHMinusThreeProkhorovWeakConvergence

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology ProbabilityTheory Filter

/-- Explicit inputs for constructing a free-field candidate by the
Prokhorov/subsequence route. The extraction and finite-cylinder identification
are kept as named analytic inputs; they are not inferred from finite-dimensional
Gaussian laws alone. -/
structure PeriodicHMinusThreeFreeFieldExistenceInput
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) where
  μ : ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion
  tightness : IsTightMeasureSet
    {ρ : Measure PeriodicHMinusThreeCompletion | ∃ n, ρ = μ n}
  prokhorov_extraction :
    ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∃ (ms : ℕ → ℕ) (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion),
        Tendsto (fun k => μ (ns (ms k))) atTop (𝓝 ν)
  extracted_limit_has_expected_finite_fourier_marginals :
    ∀ (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
      (ms : ℕ → ℕ) (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion),
      Tendsto (fun k => μ (ns (ms k))) atTop (𝓝 ν) →
      ∀ (m : ℕ) (modes : Fin m → PeriodicFourierIndex),
        ν.map (f := periodicHMinusThreeCylinderMap m modes)
            ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
          (periodicResolventTargetProbabilityMeasure 2
            (Fintype.card (Fin m × Bool)) L mass hmass
            (periodicHMinusThreeCylinderTestFamily m L hL modes)).map
            (f := periodicHMinusThreeComplexifyCylinder m modes)
            ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable)

/-- A genuine Borel probability measure on the completed H^-3 carrier, chosen
from the Prokhorov limit of the identity subsequence. -/
noncomputable def periodicHMinusThreeFreeFieldCandidate
    (I : PeriodicHMinusThreeFreeFieldExistenceInput L mass hL hmass) :
    ProbabilityMeasure PeriodicHMinusThreeCompletion :=
  Classical.choose (Classical.choose_spec (I.prokhorov_extraction id tendsto_id))

/-- The chosen candidate is an actual infinite-dimensional probability measure,
not merely a compatible family of finite-dimensional laws. -/
theorem periodicHMinusThreeFreeFieldCandidate_has_expected_finite_fourier_marginals
    (I : PeriodicHMinusThreeFreeFieldExistenceInput L mass hL hmass)
    (m : ℕ) (modes : Fin m → PeriodicFourierIndex) :
    (periodicHMinusThreeFreeFieldCandidate I).map
        (f := periodicHMinusThreeCylinderMap m modes)
        ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
      (periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map
        (f := periodicHMinusThreeComplexifyCylinder m modes)
        ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable) := by
  have hν := Classical.choose_spec
    (Classical.choose_spec (I.prokhorov_extraction id tendsto_id))
  exact I.extracted_limit_has_expected_finite_fourier_marginals
    id tendsto_id (Classical.choose (I.prokhorov_extraction id tendsto_id))
    (Classical.choose (Classical.choose_spec
      (I.prokhorov_extraction id tendsto_id))) hν m modes

end Pphi2Clean.Continuum
