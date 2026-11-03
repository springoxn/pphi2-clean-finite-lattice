import AImathPPhi2Clean.PeriodicHMinusThreeFreeFieldCandidate
import AImathPPhi2Clean.PeriodicHMinusThreeTopologyBorel

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology ProbabilityTheory Filter

/-- Finite Fourier cylinder marginals determine the full Borel probability
measure on the completed periodic H^-3 carrier. The Borel-generation theorem is
instantiated from the explicit Polish input, and the final equality is obtained
by the cylinder pi-system measure-uniqueness theorem. -/
theorem periodicHMinusThree_subsequence_limit_eq_free_of_cylinder_marginals
    {L mass : ℝ} {hL : 0 < L} {hmass : 0 < mass}
    (hpolish : PeriodicHMinusThreePolishInput)
    (I : PeriodicHMinusThreeFreeFieldExistenceInput L mass hL hmass)
    (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (hmarg : ∀ (s : Finset PeriodicFourierIndex),
      ν.map (f := (fun x : PeriodicHMinusThreeCompletion =>
        s.restrict (x : PeriodicFourierIndex → ℂ)))
        ((Finset.measurable_restrict s).comp
          measurable_periodicHMinusThree_coordinate_inclusion).aemeasurable =
      (periodicHMinusThreeFreeFieldCandidate I).map
        (f := (fun x : PeriodicHMinusThreeCompletion =>
          s.restrict (x : PeriodicFourierIndex → ℂ)))
        ((Finset.measurable_restrict s).comp
          measurable_periodicHMinusThree_coordinate_inclusion).aemeasurable) :
    ν = periodicHMinusThreeFreeFieldCandidate I := by
  have hgen : PeriodicHMinusThreeCylinderBorelGenerationInput :=
    periodicHMinusThree_cylinder_sigma_eq_borel_of_polish hpolish
  exact periodicHMinusThree_probabilityMeasure_ext_of_finite_marginals
    hgen ν (periodicHMinusThreeFreeFieldCandidate I) hmarg

end Pphi2Clean.Continuum
