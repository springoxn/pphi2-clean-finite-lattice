import AImathPPhi2Clean.ActualWeakLimitArbitraryDim
noncomputable section
namespace Pphi2Clean.ArbitraryDimContract
open MeasureTheory ProbabilityTheory Topology Filter
open Pphi2Clean.ArbitraryDim Pphi2Clean.ArbitraryDimGaussian

def parameters (d : ℕ) (hd : 0 < d) (r : ℝ) (hr : (d : ℝ) / 2 < r) : Parameters :=
  ⟨d, hd, r, hr, 1, by norm_num⟩

/-- Actual probability-measure weak convergence in every positive dimension,
with source order r>d/2 and target order r+1, uniquely specified by the
continuum Fourier Gaussian finite marginals. -/
theorem arbitrary_dimensional_actual_raw_gaussian_weak_convergence
    (d : ℕ) (hd : 0 < d) (r : ℝ) (hr : (d : ℝ) / 2 < r)
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    letI : Parameters := parameters d hd r hr
    ∃! ν : ProbabilityMeasure TargetCompletion,
      Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop (𝓝 ν) ∧
      ∀ s : Finset Index, ν.map (targetFiniteCoordinates s) =
        targetFiniteGaussianLimit s L mass hL hmass := by
  letI : Parameters := parameters d hd r hr
  exact actualTarget_fixedVolume_weak_limit_existsUnique L mass hL hmass

/-- A convenient real exponent valid uniformly for all positive dimensions. -/
def defaultParameters (d : ℕ) (hd : 0 < d) : Parameters :=
  parameters d hd (((d : ℝ) + 1) / 2) (by linarith)

example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    letI : Parameters := defaultParameters 1 (by decide)
    ∃ ν : ProbabilityMeasure TargetCompletion,
      Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop (𝓝 ν) := by
  letI : Parameters := defaultParameters 1 (by decide)
  exact actualTarget_fixedVolume_weak_limit_exists L mass hL hmass

example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    letI : Parameters := defaultParameters 2 (by decide)
    ∃ ν : ProbabilityMeasure TargetCompletion,
      Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop (𝓝 ν) := by
  letI : Parameters := defaultParameters 2 (by decide)
  exact actualTarget_fixedVolume_weak_limit_exists L mass hL hmass

example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    letI : Parameters := parameters 122409 (by decide) 61205 (by norm_num)
    ∃ ν : ProbabilityMeasure TargetCompletion,
      Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop (𝓝 ν) := by
  letI : Parameters := parameters 122409 (by decide) 61205 (by norm_num)
  exact actualTarget_fixedVolume_weak_limit_exists L mass hL hmass

#check @arbitrary_dimensional_actual_raw_gaussian_weak_convergence
#check @actualRawAtomicLift_eq_rawAtomicFourierLift
#check @actualTargetLift_apply
#check @targetFiniteGaussianLimit_isGaussian
#print axioms arbitrary_dimensional_actual_raw_gaussian_weak_convergence
#print axioms actualRawAtomicLift_eq_rawAtomicFourierLift
#print axioms actualTargetLift_apply
#print axioms targetFiniteGaussianLimit_isGaussian
end Pphi2Clean.ArbitraryDimContract
