import AImathPPhi2Clean.PolynomialMomentTightness

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory

/-- A uniform second-moment estimate in a continuous seminorm plus polynomial
basis growth supplies the coordinate moment hypothesis used by the concrete
weak-dual tightness theorem. -/
theorem basis_moment_bound_of_seminorm_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [MeasurableSpace (WeakDual ℝ E)]
    {ι : Type*} (μ : ι → Measure (WeakDual ℝ E)) (basis : ℕ → E)
    (p : Seminorm ℝ E) (M D : ℝ) (s : ℕ) (hM : 0 ≤ M)
    (hgrowth : ∀ n, p (basis n) ≤ D * (1 + (n : ℝ)) ^ s)
    (hbound : ∀ f i, ∫ ω, ω f ^ 2 ∂(μ i) ≤ M * p f ^ 2) :
    ∀ n i, ∫ ω, ω (basis n) ^ 2 ∂(μ i) ≤
      (M * D ^ 2) * (1 + (n : ℝ)) ^ (2 * s) := by
  intro n i
  calc
    ∫ ω, ω (basis n) ^ 2 ∂(μ i) ≤ M * p (basis n) ^ 2 := hbound _ _
    _ ≤ M * (D * (1 + (n : ℝ)) ^ s) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact pow_le_pow_left₀ (apply_nonneg p _) (hgrowth n) 2
    _ = (M * D ^ 2) * (1 + (n : ℝ)) ^ (2 * s) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm s 2]
      ring

end Pphi2Clean.Continuum
