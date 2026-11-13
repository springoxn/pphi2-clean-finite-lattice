import Mathlib.MeasureTheory.Measure.LevyConvergence

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology ProbabilityTheory

/-- The abstract data needed to identify an infinite-dimensional weak limit from
its finite cylinder marginals. `Ω` is intended to be the completed H⁻s or
periodic distribution space. -/
structure PeriodicFullSpaceWeakLimitBridge where
  Ω : Type*
  instMeasurableΩ : MeasurableSpace Ω
  instTopologicalΩ : TopologicalSpace Ω
  μ : ℕ → Measure Ω
  instMeasureTopological : TopologicalSpace (Measure Ω)
  μfree : Measure Ω
  tightness : Prop
  finite_marginal_unique : Prop
  cylinder_sigma_generates : Prop
  subsequential_limit_exists : Prop
  every_subsequential_limit_is_free : Prop

attribute [instance] PeriodicFullSpaceWeakLimitBridge.instMeasurableΩ
  PeriodicFullSpaceWeakLimitBridge.instTopologicalΩ
  PeriodicFullSpaceWeakLimitBridge.instMeasureTopological

/-- The full-space weak-convergence conclusion represented by the bridge. -/
def PeriodicFullSpaceWeakConvergenceConclusion
    (B : PeriodicFullSpaceWeakLimitBridge) : Prop :=
  Filter.Tendsto B.μ Filter.atTop (𝓝 B.μfree)

/-- The concrete logical shape of the final identification step. Once tightness
supplies subsequential limits and cylinder uniqueness identifies every such
limit with `μfree`, the desired statement is convergence of the whole sequence.
The field `full_tendsto` is deliberately an explicit formalization boundary:
this project does not yet provide the Prokhorov/cylinder-generation theorem
that derives it from the preceding four propositions. -/
structure PeriodicFullSpaceWeakConvergenceInput
    (B : PeriodicFullSpaceWeakLimitBridge) where
  full_tendsto : PeriodicFullSpaceWeakConvergenceConclusion B

theorem periodicFullSpace_weak_tendsto_of_identification_input
    (B : PeriodicFullSpaceWeakLimitBridge)
    (hB : PeriodicFullSpaceWeakConvergenceInput B) :
    Filter.Tendsto B.μ Filter.atTop (𝓝 B.μfree) := by
  simpa [PeriodicFullSpaceWeakConvergenceConclusion] using hB.full_tendsto

end Pphi2Clean.Continuum
