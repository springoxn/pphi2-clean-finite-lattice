import AImathPPhi2Clean.TargetFiniteMarginal122409

set_option maxRecDepth 500000
set_option maxHeartbeats 0
noncomputable section
namespace Pphi2Clean.Dim122409Gaussian
open MeasureTheory ProbabilityTheory Topology Filter

/-- Whole-sequence convergence of the actual raw atomic Gaussian lift, for every
positive lattice scale N=n+1, in the weighted target completion at d=122409. -/
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

/-- Assessment of the optional stronger endpoint: the existing real-rpow
weights admit a summable source exponent 61204.75 < 61205. The convergence
endpoint above retains the requested default target exponent 61206. -/
theorem fractionalSourceWeight_summable :
    Summable (fun k : Index => (1 + ‖k‖) ^ (-2 * (61204 + 3 / 4 : ℝ))) := by
  let p : ℝ := 2 * (61204 + 3 / 4 : ℝ)
  let q : ℝ := p / (122409 : ℝ)
  have hq : 1 < q := by norm_num [p, q]
  apply Summable.of_nonneg_of_le
  · intro k
    exact Real.rpow_nonneg (by positivity) _
  · intro k
    simpa [p, q] using Pphi2Clean.DimensionFreeProbe.radial_weight_le_productWeight
      (d := 122409) (by norm_num) p (by positivity) k
  · simpa [p, q] using Pphi2Clean.DimensionFreeProbe.productWeight_summable q hq 122409

theorem fractionalSource_to_61205_weight_ratio (k : Index) :
    (1 + ‖k‖) ^ (-2 * (61205 : ℝ)) =
      (1 + ‖k‖) ^ (-(1 / 2 : ℝ)) *
        (1 + ‖k‖) ^ (-2 * (61204 + 3 / 4 : ℝ)) := by
  rw [← Real.rpow_add (by positivity : 0 < 1 + ‖k‖)]
  congr 1
  norm_num

#print axioms fractionalSourceWeight_summable
#print axioms actualTarget_fixedVolume_weak_tendsto_gaussianLimit
#print axioms actualTargetGaussianLimit_finite_marginal
#print axioms actualTarget_fixedVolume_weak_limit_existsUnique
end Pphi2Clean.Dim122409Gaussian
