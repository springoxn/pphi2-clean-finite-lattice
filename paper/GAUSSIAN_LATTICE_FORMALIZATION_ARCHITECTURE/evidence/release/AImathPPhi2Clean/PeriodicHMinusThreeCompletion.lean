import AImathPPhi2Clean.PeriodicNegativeSobolevCarriers
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

noncomputable section

namespace Pphi2Clean.Continuum

/-- Fourier labels for the two-dimensional periodic torus. -/
abbrev PeriodicFourierIndex := Fin 2 → ℤ

/-- The concrete H^-3 realization: coefficients multiplied by the square-root
Sobolev weight form an ℓ² sequence. Mathlib supplies its complete normed topology. -/
abbrev PeriodicHMinusThreeCompletion :=
  lp (fun _ : PeriodicFourierIndex => ℂ) 2

/-- The weighted Fourier sequence associated with raw distribution coefficients. -/
def periodicHMinusThreeWeightedCoefficients
    (c : PeriodicFourierIndex → ℂ) : PeriodicFourierIndex → ℂ :=
  fun k => (Real.sqrt (periodicHMinusThreeWeight k) : ℂ) * c k

/-- Decode a completed weighted sequence into distributional Fourier coefficients.
This map is total; division uses the canonical complex-field convention at zero. -/
def periodicHMinusThreeDistributionCoefficients
    (x : PeriodicHMinusThreeCompletion) : PeriodicFourierIndex → ℂ :=
  fun k => x k / (Real.sqrt (periodicHMinusThreeWeight k) : ℂ)

/-- Each Fourier coordinate is continuous in the completed H^-3 topology. -/
theorem continuous_periodicHMinusThree_coordinate (k : PeriodicFourierIndex) :
    Continuous (fun x : PeriodicHMinusThreeCompletion => x k) := by
  exact (lp.evalCLM ℝ (fun _ : PeriodicFourierIndex => ℂ) 2 k).continuous

/-- Finite Fourier-coordinate cylinder projection on the concrete weighted `lp`
completion. Its coordinates are the weighted coefficients stored by the completion. -/
def periodicHMinusThreeCylinderMap (m : ℕ)
    (modes : Fin m → PeriodicFourierIndex) :
    PeriodicHMinusThreeCompletion → Fin m → ℂ :=
  fun x i => x (modes i)

theorem continuous_periodicHMinusThree_cylinderMap (m : ℕ)
    (modes : Fin m → PeriodicFourierIndex) :
    Continuous (periodicHMinusThreeCylinderMap m modes) := by
  apply continuous_pi
  intro i
  exact continuous_periodicHMinusThree_coordinate (modes i)

theorem periodicHMinusThreeCylinderMap_apply (m : ℕ)
    (modes : Fin m → PeriodicFourierIndex)
    (x : PeriodicHMinusThreeCompletion) (i : Fin m) :
    periodicHMinusThreeCylinderMap m modes x i = x (modes i) := rfl

instance : MeasurableSpace PeriodicHMinusThreeCompletion :=
  borel PeriodicHMinusThreeCompletion

instance : BorelSpace PeriodicHMinusThreeCompletion := ⟨rfl⟩

instance instMeasurableSpaceFiniteComplexCoordinates (m : ℕ) :
    MeasurableSpace (Fin m → ℂ) := by
  letI : ∀ i : Fin m, MeasurableSpace ℂ := fun _ => inferInstance
  exact MeasurableSpace.pi

theorem measurable_periodicHMinusThree_cylinderMap (m : ℕ)
    (modes : Fin m → PeriodicFourierIndex) :
    Measurable (periodicHMinusThreeCylinderMap m modes) :=
  (continuous_periodicHMinusThree_cylinderMap m modes).measurable

theorem periodicHMinusThree_completion_is_borel :
    BorelSpace PeriodicHMinusThreeCompletion := inferInstance

end Pphi2Clean.Continuum
