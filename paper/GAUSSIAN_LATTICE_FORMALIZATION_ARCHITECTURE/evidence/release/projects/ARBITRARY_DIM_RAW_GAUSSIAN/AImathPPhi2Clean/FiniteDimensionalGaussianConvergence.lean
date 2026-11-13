import AImathPPhi2Clean.PhysicalLatticeGaussianLaw
import Mathlib.MeasureTheory.Measure.LevyConvergence

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory

/-- Finite-dimensional weak convergence is exactly the Levy characteristic-function
criterion. The characteristic-function convergence remains an explicit input here;
this bridge does not hide covariance or Sobolev assumptions. -/
theorem finiteDimensional_weak_tendsto_of_charFun
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) (μ₀ : ProbabilityMeasure E)
    (hchar : ∀ t : E,
      Filter.Tendsto (fun n => charFun (μ n) t) Filter.atTop
        (nhds (charFun μ₀ t))) :
    Filter.Tendsto μ Filter.atTop (nhds μ₀) := by
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr hchar

end Pphi2Clean.Continuum
