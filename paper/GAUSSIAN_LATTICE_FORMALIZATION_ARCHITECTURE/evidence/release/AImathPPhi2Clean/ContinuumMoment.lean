import Mathlib

noncomputable section

namespace Pphi2Clean.Continuum

open MeasureTheory

/-- A uniform bounded-continuous moment estimate passes to a weak limit.
This is a property-inheritance interface; it does not assert that a weak limit
exists. -/
theorem uniform_integral_bound_passes_to_weak_limit
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (g : X → ℝ)
    (μ : ℕ → Measure X) (μ_lim : Measure X) (C : ℝ)
    (h_bound : ∀ n, ∫ x, g x ∂(μ n) ≤ C)
    (h_weak : Filter.Tendsto (fun n => ∫ x, g x ∂(μ n)) Filter.atTop
      (nhds (∫ x, g x ∂μ_lim))) :
    ∫ x, g x ∂μ_lim ≤ C := by
  exact le_of_tendsto h_weak (.of_forall h_bound)

end Pphi2Clean.Continuum
