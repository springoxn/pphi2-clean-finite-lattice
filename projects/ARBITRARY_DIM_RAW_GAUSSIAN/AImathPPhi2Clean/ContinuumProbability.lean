import Mathlib

noncomputable section

namespace Pphi2Clean.Continuum

open MeasureTheory

/-- A measurable pushforward of a probability measure is again a probability
measure. This is the measure-theoretic core of the continuum embedding step. -/
theorem map_preserves_probability
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → Y) (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (Measure.map f μ) := by
  exact (Measure.isProbabilityMeasure_map_iff hf).2 inferInstance

end Pphi2Clean.Continuum
