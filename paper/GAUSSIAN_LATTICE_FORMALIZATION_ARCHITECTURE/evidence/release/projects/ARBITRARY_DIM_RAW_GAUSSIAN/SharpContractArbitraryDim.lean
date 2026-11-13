import AImathPPhi2Clean.ActualWeakLimitArbitraryDim
noncomputable section
namespace Pphi2Clean.ArbitraryDimContract
open MeasureTheory ProbabilityTheory Topology Filter
open Pphi2Clean.ArbitraryDim Pphi2Clean.ArbitraryDimGaussian

/-- Source order strictly between d/2 and the requested target s. -/
abbrev sharpSourceOrder (d : ℕ) (s : ℝ) : ℝ := (s + (d : ℝ) / 2) / 2
@[instance_reducible] def sharpParameters (d : ℕ) (hd : 0 < d)
    (s : ℝ) (hs : (d : ℝ) / 2 < s) : Parameters where
  dimension := d
  dimension_pos := hd
  energyOrder := sharpSourceOrder d s
  energyOrder_gt := by dsimp [sharpSourceOrder]; linarith
  gap := s - sharpSourceOrder d s
  gap_pos := by dsimp [sharpSourceOrder]; linarith

/-- The weighted target is exactly the requested real Sobolev order s. -/
theorem sharp_target_weight (d : ℕ) (hd : 0 < d) (s : ℝ)
    (hs : (d : ℝ) / 2 < s) :
    letI : Parameters := sharpParameters d hd s hs
    ∀ k : Fin d → ℤ, targetWeight k = (1 + ‖k‖) ^ (-2 * s) := by
  letI : Parameters := sharpParameters d hd s hs
  intro k
  unfold targetWeight energyOrder gap
  change (1 + ‖k‖) ^ (-2 * (sharpSourceOrder d s + (s - sharpSourceOrder d s))) = _
  congr 2
  ring

/-- Full-sequence weak convergence of the actual raw atomic Gaussian
probability measures, in every positive dimension at every real order s>d/2.
The continuum Fourier Gaussian finite marginals specify the limit uniquely. -/
theorem sharp_actual_raw_gaussian_weak_convergence
    (d : ℕ) (hd : 0 < d) (s : ℝ) (hs : (d : ℝ) / 2 < s)
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    letI : Parameters := sharpParameters d hd s hs
    ∃! ν : ProbabilityMeasure TargetCompletion,
      Tendsto (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass) atTop (𝓝 ν) ∧
      ∀ t : Finset Index, ν.map (targetFiniteCoordinates t) =
        targetFiniteGaussianLimit t L mass hL hmass := by
  letI : Parameters := sharpParameters d hd s hs
  exact actualTarget_fixedVolume_weak_limit_existsUnique L mass hL hmass

example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :=
  sharp_actual_raw_gaussian_weak_convergence 1 (by decide) 1 (by norm_num) L mass hL hmass
example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :=
  sharp_actual_raw_gaussian_weak_convergence 2 (by decide) (3/2) (by norm_num) L mass hL hmass
example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :=
  sharp_actual_raw_gaussian_weak_convergence 122409 (by decide) 61206 (by norm_num) L mass hL hmass

#check @sharp_actual_raw_gaussian_weak_convergence
#check @sharp_target_weight
#check @actualRawAtomicLift_eq_rawAtomicFourierLift
#check @actualTargetLift_apply
#check @targetFiniteGaussianLimit_isGaussian
#print axioms sharp_actual_raw_gaussian_weak_convergence
#print axioms sharp_target_weight
#print axioms actualRawAtomicLift_eq_rawAtomicFourierLift
#print axioms actualTargetLift_apply
#print axioms targetFiniteGaussianLimit_isGaussian
end Pphi2Clean.ArbitraryDimContract
