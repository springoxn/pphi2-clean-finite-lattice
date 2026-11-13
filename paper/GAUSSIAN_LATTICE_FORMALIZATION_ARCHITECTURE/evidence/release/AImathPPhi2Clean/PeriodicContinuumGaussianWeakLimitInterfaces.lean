import AImathPPhi2Clean.PhysicalLatticeSampling
import AImathPPhi2Clean.PeriodicNegativeSobolevCarriers
import AImathPPhi2Clean.PeriodicFullHMinusTwoTraceConcrete
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
abbrev PeriodicHMinusThreeSpace :=
  {c : (Fin 2 → ℤ) → ℂ // c ∈ periodicHMinusThreeCarrier}
structure PeriodicContinuumGaussianConstructionData where
  measure : Measure PeriodicHMinusThreeSpace
  probability : IsProbabilityMeasure measure
structure PeriodicPhysicalLatticeMeasureData where
  measure : Measure PeriodicHMinusThreeSpace
  probability : IsProbabilityMeasure measure
structure PeriodicPhysicalFreeFieldWeakLimitData where
  limit : Measure PeriodicHMinusThreeSpace
  probability : IsProbabilityMeasure limit
end Pphi2Clean.Continuum
