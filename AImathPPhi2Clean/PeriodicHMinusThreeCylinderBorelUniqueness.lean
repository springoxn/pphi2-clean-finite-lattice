import AImathPPhi2Clean.PeriodicHMinusThreeCylinderConvergence
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

noncomputable section

namespace Pphi2Clean.Continuum

open MeasureTheory Set

/-- Finite-coordinate cylinder event pulled back from the ambient product of
Fourier coefficients to the concrete weighted `lp` carrier. -/
def periodicHMinusThreeCoordinateCylinder
    (s : Finset PeriodicFourierIndex)
    (S : Set (∀ i : s, ℂ)) : Set PeriodicHMinusThreeCompletion :=
  (fun x : PeriodicHMinusThreeCompletion =>
    s.restrict (x : PeriodicFourierIndex → ℂ)) ⁻¹' S

/-- All measurable finite-coordinate cylinders, represented as pullbacks of the
standard product-space measurable cylinders. -/
def periodicHMinusThreeMeasurableCylinders : Set (Set PeriodicHMinusThreeCompletion) :=
  {A | ∃ t ∈ measurableCylinders (fun _ : PeriodicFourierIndex => ℂ),
    (fun x : PeriodicHMinusThreeCompletion => (x : PeriodicFourierIndex → ℂ)) ⁻¹' t = A}

theorem isPiSystem_periodicHMinusThreeMeasurableCylinders :
    IsPiSystem periodicHMinusThreeMeasurableCylinders := by
  exact (isPiSystem_measurableCylinders.comap
    (fun x : PeriodicHMinusThreeCompletion =>
      (x : PeriodicFourierIndex → ℂ)))

theorem periodicHMinusThreeCoordinateCylinder_mem
    (s : Finset PeriodicFourierIndex)
    {S : Set (∀ i : s, ℂ)} (hS : MeasurableSet S) :
    periodicHMinusThreeCoordinateCylinder s S ∈
      periodicHMinusThreeMeasurableCylinders := by
  refine ⟨cylinder s S, ?_, ?_⟩
  · rw [mem_measurableCylinders]
    exact ⟨s, S, hS, rfl⟩
  · rfl

/-- The coordinate inclusion into the ambient product is measurable for the
carrier's declared Borel structure. -/
theorem measurable_periodicHMinusThree_coordinate_inclusion :
    Measurable (fun x : PeriodicHMinusThreeCompletion =>
      (x : PeriodicFourierIndex → ℂ)) := by
  rw [measurable_pi_iff]
  intro k
  exact (continuous_periodicHMinusThree_coordinate k).measurable

/-- The carrier-specific Borel-generation proposition is kept as an explicit
interface. Its concrete proof for this `lp` carrier is supplied by
`periodicHMinusThree_cylinder_sigma_eq_borel_of_polish` in
`PeriodicHMinusThreeTopologyBorel.lean`. -/
def PeriodicHMinusThreeCylinderBorelGenerationInput : Prop :=
  MeasurableSpace.generateFrom periodicHMinusThreeMeasurableCylinders =
    borel PeriodicHMinusThreeCompletion

theorem periodicHMinusThree_cylinder_sigma_le_borel :
    MeasurableSpace.generateFrom periodicHMinusThreeMeasurableCylinders ≤
      borel PeriodicHMinusThreeCompletion := by
  refine MeasurableSpace.generateFrom_le ?_
  intro A hA
  rcases hA with ⟨t, ht, rfl⟩
  exact (MeasurableSet.of_mem_measurableCylinders ht).preimage
    measurable_periodicHMinusThree_coordinate_inclusion

theorem measurableSet_periodicHMinusThreeCoordinateCylinder
    (s : Finset PeriodicFourierIndex)
    {S : Set (∀ i : s, ℂ)} (hS : MeasurableSet S) :
    MeasurableSet (periodicHMinusThreeCoordinateCylinder s S) := by
  exact hS.preimage
    ((Finset.measurable_restrict s).comp
      measurable_periodicHMinusThree_coordinate_inclusion)

/-- Two finite measures agreeing on all finite-coordinate cylinders agree on
all Borel sets, assuming the named Borel-generation input. -/
theorem periodicHMinusThree_measure_ext_of_cylinder
    (hgen : PeriodicHMinusThreeCylinderBorelGenerationInput)
    (μ ν : Measure PeriodicHMinusThreeCompletion)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : ∀ (s : Finset PeriodicFourierIndex), ∀ (S : Set (∀ i : s, ℂ)),
      MeasurableSet S →
        μ (periodicHMinusThreeCoordinateCylinder s S) =
          ν (periodicHMinusThreeCoordinateCylinder s S))
    (huniv : μ univ = ν univ) :
    μ = ν := by
  apply ext_of_generate_finite periodicHMinusThreeMeasurableCylinders hgen.symm
    isPiSystem_periodicHMinusThreeMeasurableCylinders
  · intro A hA
    rcases hA with ⟨t, ht, rfl⟩
    rcases (mem_measurableCylinders t).mp ht with ⟨s, S, hS, rfl⟩
    exact hμν s S hS
  · exact huniv

/-- Equality of all finite coordinate pushforward laws implies equality of the
underlying Borel probability measures. -/
theorem periodicHMinusThree_probabilityMeasure_ext_of_finite_marginals
    (hgen : PeriodicHMinusThreeCylinderBorelGenerationInput)
    (μ ν : ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (hmarg : ∀ (s : Finset PeriodicFourierIndex),
      μ.map (f := (fun x : PeriodicHMinusThreeCompletion =>
        s.restrict (x : PeriodicFourierIndex → ℂ)))
        ((Finset.measurable_restrict s).comp
          measurable_periodicHMinusThree_coordinate_inclusion).aemeasurable =
      ν.map (f := (fun x : PeriodicHMinusThreeCompletion =>
        s.restrict (x : PeriodicFourierIndex → ℂ)))
        ((Finset.measurable_restrict s).comp
          measurable_periodicHMinusThree_coordinate_inclusion).aemeasurable) :
    μ = ν := by
  apply Subtype.ext
  apply periodicHMinusThree_measure_ext_of_cylinder hgen
    (μ := μ) (ν := ν)
  · intro s S hS
    have hmeas : Measurable (fun x : PeriodicHMinusThreeCompletion =>
        s.restrict (x : PeriodicFourierIndex → ℂ)) :=
      (Finset.measurable_restrict s).comp
        measurable_periodicHMinusThree_coordinate_inclusion
    change (μ : Measure PeriodicHMinusThreeCompletion)
        (periodicHMinusThreeCoordinateCylinder s S) =
      (ν : Measure PeriodicHMinusThreeCompletion)
        (periodicHMinusThreeCoordinateCylinder s S)
    rw [periodicHMinusThreeCoordinateCylinder]
    rw [← Measure.map_apply hmeas hS, ← Measure.map_apply hmeas hS]
    exact congrArg
      (fun ρ : ProbabilityMeasure (∀ i : s, ℂ) =>
        (ρ : Measure (∀ i : s, ℂ)) S) (hmarg s)
  · simp

end Pphi2Clean.Continuum
