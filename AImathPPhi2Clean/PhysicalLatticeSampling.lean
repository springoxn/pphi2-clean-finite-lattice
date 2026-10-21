import AImathPPhi2Clean.PhysicalLatticeGaussianBound
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section
namespace Pphi2Clean.Continuum
open Pphi2Clean.UpstreamLattice MeasureTheory ProbabilityTheory

/-- Physical point represented by a periodic lattice site, in `[0,a*N)^d`. -/
def latticePhysicalPoint (d N : ℕ) [NeZero N] (a : ℝ)
    (x : FinLatticeSites d N) : Fin d → ℝ :=
  fun i => a * ((x i).val : ℝ)

/-- Actual Riemann-sum sampling of a bounded continuous test function. -/
def physicalTestEval (d N : ℕ) [NeZero N] (a : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites d N))) :
    (BoundedContinuousFunction (Fin d → ℝ) ℝ) →L[ℝ] ℝ :=
  (a ^ d) • BoundedContinuousFunction.evalCLM ℝ
    (latticePhysicalPoint d N a ((Fintype.equivFin (FinLatticeSites d N)).symm j))

/-- The discrete test seminorm is uniformly controlled by the supremum norm
and physical volume. No regularity or Riemann-sum limit is assumed. -/
theorem sampled_testSeminormSq_le (d N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    latticeTestSeminormSq d N a (fun x => f (latticePhysicalPoint d N a x)) ≤
      (a * (N : ℝ)) ^ d * ‖f‖ ^ 2 := by
  unfold latticeTestSeminormSq
  have hpoint : ∀ x : FinLatticeSites d N,
      (f (latticePhysicalPoint d N a x)) ^ 2 ≤ ‖f‖ ^ 2 := by
    intro x
    have hh := f.norm_coe_le_norm (latticePhysicalPoint d N a x)
    have hn := norm_nonneg f
    rw [Real.norm_eq_abs] at hh
    nlinarith [sq_abs (f (latticePhysicalPoint d N a x)), abs_nonneg (f (latticePhysicalPoint d N a x))]
  calc
    _ ≤ a ^ d * ∑ x : FinLatticeSites d N, ‖f‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (pow_pos ha d))
      exact Finset.sum_le_sum (fun x hx => hpoint x)
    _ = (a * (N : ℝ)) ^ d * ‖f‖ ^ 2 := by
      simp [FinLatticeSites, mul_pow, Nat.cast_pow, mul_assoc]

/-- Actual finite Gaussian law pushed to test-function configurations with
physical lattice locations and the Riemann weights `a^d`. -/
def physicalGJMeasure (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Measure (WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ)) :=
  (finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ d N a mass ha hmass)).map
    (latticeEmbedLift (physicalTestEval d N a))

instance physicalGJMeasure_probability (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (physicalGJMeasure d N a mass ha hmass) := by
  unfold physicalGJMeasure
  infer_instance

/-- Concrete second-moment estimate for the physically sampled GJ field. -/
theorem physicalGJMeasure_second_moment_le (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∫ ω, (ω f) ^ 2 ∂physicalGJMeasure d N a mass ha hmass ≤
      mass⁻¹ ^ 2 * ((a * (N : ℝ)) ^ d * ‖f‖ ^ 2) := by
  have h := latticeCovarianceGJ_sampled_second_moment_le d N a mass ha hmass
    (fun x => f (latticePhysicalPoint d N a x))
  have hs := sampled_testSeminormSq_le d N a ha f
  have hb := mul_le_mul_of_nonneg_left hs (sq_nonneg mass⁻¹)
  apply le_trans ?_ hb
  unfold physicalGJMeasure
  rw [numberedLatticeCovarianceGJ_lift_second_moment]
  rw [latticeCovarianceGJ_inner, latticeCovariance_inner] at h
  simpa [physicalTestEval, physicalLatticeSample, pow_two, mul_assoc] using h

/-- UV-uniform bound at fixed physical edge length. -/
theorem physicalGJMeasure_fixed_volume_second_moment_le (d N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∫ ω, (ω f) ^ 2 ∂physicalGJMeasure d N a mass ha hmass ≤
      mass⁻¹ ^ 2 * L ^ d * ‖f‖ ^ 2 := by
  have h := physicalGJMeasure_second_moment_le d N a mass ha hmass f
  rw [hL] at h
  simpa [mul_assoc] using h

end Pphi2Clean.Continuum
