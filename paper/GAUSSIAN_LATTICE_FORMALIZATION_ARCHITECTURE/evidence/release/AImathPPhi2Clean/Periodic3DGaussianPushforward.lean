import AImathPPhi2Clean.Periodic3DWeightedFiniteSource
import AImathPPhi2Clean.Periodic3DFixedModeCovariance
import AImathPPhi2Clean.PhysicalLatticeGaussianLaw

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

def periodic3DFiniteSourceGaussianMeasure (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure Periodic3DCompletion :=
  Measure.map (periodic3DFiniteSourceFourierLift N a L)
    (finiteCovarianceGaussianMeasure
      (numberedLatticeCovarianceGJ 3 N a mass ha hmass))

instance periodic3DFiniteSourceGaussianMeasure_isProbability (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (periodic3DFiniteSourceGaussianMeasure N a mass L ha hmass) := by
  unfold periodic3DFiniteSourceGaussianMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_periodic3DFiniteSourceFourierLift N a L).aemeasurable).2 inferInstance

theorem periodic3DFiniteSourceGaussianMeasure_apply (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (s : Set Periodic3DCompletion) (hs : MeasurableSet s) :
    periodic3DFiniteSourceGaussianMeasure N a mass L ha hmass s =
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 3 N a mass ha hmass)
        ((periodic3DFiniteSourceFourierLift N a L) ⁻¹' s) := by
  rw [periodic3DFiniteSourceGaussianMeasure]
  exact Measure.map_apply
    (measurable_periodic3DFiniteSourceFourierLift N a L) hs

end Pphi2Clean.Continuum
