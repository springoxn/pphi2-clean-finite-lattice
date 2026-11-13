import AImathPPhi2Clean.WeakDualReconstruction
import AImathPPhi2Clean.PolynomialCoefficientDecay

noncomputable section
namespace Pphi2Clean.Continuum

/-- Polynomial growth boxes in the weak dual are compact under coefficient
decay controlled by a continuous seminorm and a basis expansion identity.
This discharges the summability and domination inputs of reconstruction. -/
theorem polynomial_weakDual_box_isCompact
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    (basis : ℕ → E) (coeff : ℕ → E →ₗ[ℝ] ℝ)
    (r : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (p : Seminorm ℝ E) (hp : Continuous p)
    (hdecay : ∀ f n, |coeff n f| * (1 + (n : ℝ)) ^ (r + 2) ≤ p f)
    (hexpand : ∀ (ω : WeakDual ℝ E) f,
      ω f = ∑' n, coeff n f * ω (basis n)) :
    IsCompact (observableBox (fun n (ω : WeakDual ℝ E) => ω (basis n))
      (fun n => D * (1 + (n : ℝ)) ^ r)) := by
  let S : ℝ := ∑' n : ℕ, 1 / (1 + (n : ℝ)) ^ 2
  have hS : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  let c : NNReal := ⟨D * S, mul_nonneg hD hS⟩
  let q : Seminorm ℝ E := c • p
  have hq : Continuous q := hp.const_smul c
  have hsum : ∀ f, Summable (fun n => |coeff n f| * (D * (1 + (n : ℝ)) ^ r)) := by
    intro f
    exact ((weighted_coefficients_summable (fun n => coeff n f) r (p f)
      (hdecay f)).mul_left D).congr (fun n => by ring)
  apply weakDual_coordinateBox_isCompact basis coeff _ hsum q hq _ hexpand
  intro f
  have hbound := weighted_coefficients_tsum_le (fun n => coeff n f) r (p f) (hdecay f)
  have heq : (fun n => |coeff n f| * (D * (1 + (n : ℝ)) ^ r)) =
      (fun n => D * (|coeff n f| * (1 + (n : ℝ)) ^ r)) := by
    funext n
    ring
  rw [heq, tsum_mul_left]
  calc
    D * (∑' n, |coeff n f| * (1 + (n : ℝ)) ^ r) ≤ D * (p f * S) :=
      mul_le_mul_of_nonneg_left hbound hD
    _ = q f := by
      change D * (p f * S) = (D * S) * p f
      ring

end Pphi2Clean.Continuum
