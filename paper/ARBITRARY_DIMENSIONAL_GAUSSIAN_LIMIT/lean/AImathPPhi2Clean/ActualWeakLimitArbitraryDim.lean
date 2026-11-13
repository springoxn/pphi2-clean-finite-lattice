import AImathPPhi2Clean.ArbitraryDimParameters
import AImathPPhi2Clean.TargetFiniteMarginalArbitraryDim

set_option maxRecDepth 500000
set_option maxHeartbeats 0
noncomputable section
namespace Pphi2Clean.ArbitraryDimGaussian
open Pphi2Clean.ArbitraryDim
variable [Parameters]
open MeasureTheory ProbabilityTheory Topology Filter

/-- Whole-sequence convergence of the actual raw atomic Gaussian lift, for every
positive lattice scale N=n+1, in the weighted target completion at d=dimension. -/
theorem actualTarget_fixedVolume_weak_limit_exists
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ ν : ProbabilityMeasure TargetCompletion,
      Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop (𝓝 ν) := by
  apply actualTarget_fixedVolume_exists_weak_limit_of_finite_marginal_limits L mass hL hmass
  intro s
  exact ⟨targetFiniteGaussianLimit s L mass hL hmass,
    actualTarget_fixedVolume_finite_marginal_tendsto s L mass hL hmass⟩

/-- The target measure is selected on the actual lp Borel space; its finite
Gaussian laws below characterize it uniquely. -/
def actualTargetGaussianLimit (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ProbabilityMeasure TargetCompletion :=
  (actualTarget_fixedVolume_weak_limit_exists L mass hL hmass).choose

theorem actualTarget_fixedVolume_weak_tendsto_gaussianLimit
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop
      (𝓝 (actualTargetGaussianLimit L mass hL hmass)) :=
  (actualTarget_fixedVolume_weak_limit_exists L mass hL hmass).choose_spec

theorem actualTargetGaussianLimit_finite_marginal
    (s : Finset Index) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    (actualTargetGaussianLimit L mass hL hmass).map (targetFiniteCoordinates s) =
      targetFiniteGaussianLimit s L mass hL hmass := by
  have h := (ProbabilityMeasure.continuous_map (continuous_targetFiniteCoordinates s)).continuousAt.tendsto.comp
    (actualTarget_fixedVolume_weak_tendsto_gaussianLimit L mass hL hmass)
  exact tendsto_nhds_unique h (actualTarget_fixedVolume_finite_marginal_tendsto s L mass hL hmass)

theorem actualTargetGaussianLimit_unique_of_finite_marginals
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ν : ProbabilityMeasure TargetCompletion)
    (hν : ∀ s : Finset Index, ν.map (targetFiniteCoordinates s) =
      targetFiniteGaussianLimit s L mass hL hmass) :
    ν = actualTargetGaussianLimit L mass hL hmass := by
  apply target_probabilityMeasure_ext_of_finite_marginals
  intro s
  exact (hν s).trans (actualTargetGaussianLimit_finite_marginal s L mass hL hmass).symm

theorem actualTarget_fixedVolume_weak_limit_existsUnique
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃! ν : ProbabilityMeasure TargetCompletion,
      Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop (𝓝 ν) ∧
      ∀ s : Finset Index, ν.map (targetFiniteCoordinates s) =
        targetFiniteGaussianLimit s L mass hL hmass := by
  refine ⟨actualTargetGaussianLimit L mass hL hmass, ?_, ?_⟩
  · exact ⟨actualTarget_fixedVolume_weak_tendsto_gaussianLimit L mass hL hmass,
      fun s => actualTargetGaussianLimit_finite_marginal s L mass hL hmass⟩
  · intro ν hν
    exact actualTargetGaussianLimit_unique_of_finite_marginals L mass hL hmass ν hν.2

#print axioms actualTarget_fixedVolume_weak_limit_existsUnique
end Pphi2Clean.ArbitraryDimGaussian
