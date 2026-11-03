import AImathPPhi2Clean.GaussianConfiguration

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology ProbabilityTheory
open Pphi2Clean.GaussianField

/-- An abstract enumeration of the periodic Fourier labels used by the Gaussian
series construction. The analytic fact that this enumeration covers all
`Fin 2 → ℤ` modes is intentionally an external input at this layer. -/
structure PeriodicFourierModeEnumeration where
  mode : ℕ → (Fin 2 → ℤ)
  covers : Prop

/-- The reusable existence data for an infinite-dimensional Gaussian series.
`H` is the completed Hilbert realization of the chosen weak ambient space
(for Goal 1 this is intended to be the `H⁻³` realization). -/
structure PeriodicInfiniteGaussianSeriesData where
  E : Type*
  instEAdd : AddCommGroup E
  instEModule : Module ℝ E
  instETop : TopologicalSpace E
  instEAddTop : IsTopologicalAddGroup E
  H : Type*
  instHNorm : NormedAddCommGroup H
  instHInner : InnerProductSpace ℝ H
  instHComplete : CompleteSpace H
  instHMeas : MeasurableSpace H
  instHBorel : BorelSpace H
  J : E →L[ℝ] H
  mode : PeriodicFourierModeEnumeration
  coefficientVector : ℕ → H
  coefficientSummable : Summable (fun n => ‖coefficientVector n‖)

attribute [instance] PeriodicInfiniteGaussianSeriesData.instEAdd
  PeriodicInfiniteGaussianSeriesData.instEModule
  PeriodicInfiniteGaussianSeriesData.instETop
  PeriodicInfiniteGaussianSeriesData.instEAddTop
  PeriodicInfiniteGaussianSeriesData.instHNorm
  PeriodicInfiniteGaussianSeriesData.instHInner
  PeriodicInfiniteGaussianSeriesData.instHComplete
  PeriodicInfiniteGaussianSeriesData.instHMeas
  PeriodicInfiniteGaussianSeriesData.instHBorel

/-- The finite partial-sum limit random configuration associated with the
Fourier coefficient vectors and standard iid Gaussian noise. -/
def periodicInfiniteGaussianConfiguration
    (D : PeriodicInfiniteGaussianSeriesData) :
    (ℕ → ℝ) → WeakDual ℝ D.E :=
  gaussianSeriesConfiguration D.J D.coefficientVector

/-- The resulting infinite-dimensional Gaussian measure on the weak-dual
configuration space. -/
def periodicInfiniteGaussianMeasure
    (D : PeriodicInfiniteGaussianSeriesData) : Measure (WeakDual ℝ D.E) :=
  gaussianWeakDualMeasure D.J D.coefficientVector

instance periodicInfiniteGaussianMeasure_isProbability
    (D : PeriodicInfiniteGaussianSeriesData) :
    IsProbabilityMeasure (periodicInfiniteGaussianMeasure D) := by
  unfold periodicInfiniteGaussianMeasure gaussianWeakDualMeasure
  -- named rather than `infer_instance`: the probability-measure instance for a
  -- `Measure.map` became an explicit argument in this Mathlib revision.
  exact Measure.isProbabilityMeasure_map
    (gaussianSeriesConfiguration_measurable D.J D.coefficientVector).aemeasurable

theorem periodicInfiniteGaussianConfiguration_measurable
    (D : PeriodicInfiniteGaussianSeriesData) :
    Measurable (periodicInfiniteGaussianConfiguration D) := by
  exact gaussianSeriesConfiguration_measurable D.J D.coefficientVector

/-- On the summability input, every test-function coordinate agrees almost
surely with the corresponding Gaussian Fourier series. -/
theorem periodicInfiniteGaussianConfiguration_eval_eq_tsum_ae
    (D : PeriodicInfiniteGaussianSeriesData) (f : D.E) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      periodicInfiniteGaussianConfiguration D ξ f =
        ∑' n, ξ n * @inner ℝ D.H _
          (D.coefficientVector n) (D.J f) := by
  exact gaussianSeriesConfiguration_eval_eq_tsum_ae D.J D.coefficientVector
    D.coefficientSummable f

end Pphi2Clean.Continuum
