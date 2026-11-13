import AImathPPhi2Clean.PeriodicHMinusThreeCylinderBorelUniqueness
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology ProbabilityTheory Filter

/-- The explicit remaining input for the Prokhorov/subsequence route on the
concrete periodic H^-3 carrier. The first field records the tightness input;
the second records the result of applying Prokhorov and identifying every
subsequential limit by finite cylinders. Neither field is silently inferred
from finite-coordinate convergence. -/
structure PeriodicHMinusThreeProkhorovSubsequenceIdentificationInput where
  μ : ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion
  μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion
  tightness : IsTightMeasureSet
    {ρ : Measure PeriodicHMinusThreeCompletion | ∃ n, ρ = μ n}
  every_subsequence_has_identified_subsequence :
    ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ,
        Tendsto (fun k => μ (ns (ms k))) atTop (𝓝 μfree)

/-- Once Prokhorov extraction and finite-cylinder identification have been
supplied for every subsequence, the entire probability-measure sequence
converges weakly to the identified free measure. -/
theorem periodicHMinusThree_probabilityMeasure_tendsto_of_prokhorov_subsequence_identification
    (I : PeriodicHMinusThreeProkhorovSubsequenceIdentificationInput) :
    Tendsto I.μ atTop (𝓝 I.μfree) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  exact I.every_subsequence_has_identified_subsequence ns hns

/-- A version exposing the finite-marginal uniqueness input explicitly. This
is an interface theorem: `hgen` and the cylinder uniqueness proposition must
already be supplied, while the Prokhorov extraction/identification field
remains the named analytic input above. -/
structure PeriodicHMinusThreeFullWeakConvergenceInput where
  μ : ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion
  μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion
  cylinder_borel_generation :
    PeriodicHMinusThreeCylinderBorelGenerationInput
  finite_marginal_uniqueness : Prop
  prokhorov_subsequence_identification :
    ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ,
        Tendsto (fun k => μ (ns (ms k))) atTop (𝓝 μfree)

/-- Final whole-sequence weak convergence from the explicit Prokhorov and
subsequence-identification input. The theorem does not claim that the named
Borel-generation or finite-marginal uniqueness propositions follow from the
finite-coordinate convergence theorem. -/
theorem periodicHMinusThree_full_probabilityMeasure_tendsto
    (I : PeriodicHMinusThreeFullWeakConvergenceInput) :
    Tendsto I.μ atTop (𝓝 I.μfree) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  exact I.prokhorov_subsequence_identification ns hns

/-- A decomposed input for the Prokhorov route. The extraction field is
separate from the finite-marginal identification field, so neither analytic
step is hidden inside a single convergence proposition. -/
structure PeriodicHMinusThreeProkhorovIdentificationData where
  μ : ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion
  μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion
  cylinder_borel_generation :
    PeriodicHMinusThreeCylinderBorelGenerationInput
  tightness : IsTightMeasureSet
    {ρ : Measure PeriodicHMinusThreeCompletion | ∃ n, ρ = μ n}
  prokhorov_extraction :
    ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∃ (ms : ℕ → ℕ) (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion),
        StrictMono ms ∧
        Tendsto (fun k => μ (ns (ms k))) atTop (𝓝 ν)
  extracted_limit_has_free_finite_marginals :
    ∀ (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
      (ms : ℕ → ℕ) (hms : StrictMono ms)
      (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion),
      Tendsto (fun k => μ (ns (ms k))) atTop (𝓝 ν) →
      ∀ s : Finset PeriodicFourierIndex,
        ν.map (f := (fun x : PeriodicHMinusThreeCompletion =>
          s.restrict (x : PeriodicFourierIndex → ℂ))) =
        μfree.map (f := (fun x : PeriodicHMinusThreeCompletion =>
          s.restrict (x : PeriodicFourierIndex → ℂ)))

/-- Finite-marginal uniqueness identifies every extracted Prokhorov limit with
`μfree`. -/
theorem periodicHMinusThree_identified_limit_eq_free
    (I : PeriodicHMinusThreeProkhorovIdentificationData)
    (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (hν : ∀ s : Finset PeriodicFourierIndex,
      ν.map (f := (fun x : PeriodicHMinusThreeCompletion =>
          s.restrict (x : PeriodicFourierIndex → ℂ))) =
      I.μfree.map (f := (fun x : PeriodicHMinusThreeCompletion =>
          s.restrict (x : PeriodicFourierIndex → ℂ)))) :
    ν = I.μfree := by
  exact periodicHMinusThree_probabilityMeasure_ext_of_finite_marginals
    I.cylinder_borel_generation ν I.μfree hν

/-- The decomposed Prokhorov extraction plus cylinder-identification inputs
imply weak convergence of the entire probability-measure sequence. -/
theorem periodicHMinusThree_probabilityMeasure_tendsto_of_prokhorov_extraction_and_cylinder_identification
    (I : PeriodicHMinusThreeProkhorovIdentificationData) :
    Tendsto I.μ atTop (𝓝 I.μfree) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, ν, hms, hν⟩ := I.prokhorov_extraction ns hns
  have hνmarg := I.extracted_limit_has_free_finite_marginals ns hns ms hms ν hν
  have hνeq : ν = I.μfree := periodicHMinusThree_identified_limit_eq_free I ν hνmarg
  refine ⟨ms, ?_⟩
  simpa [hνeq] using hν

end Pphi2Clean.Continuum
