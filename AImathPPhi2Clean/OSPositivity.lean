import Mathlib

noncomputable section

namespace Pphi2Clean.OS

def transfer (n : ℕ) (K : Fin n → Fin n → ℝ) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun x => ∑ y, K x y * f y

def IsPositivityImproving (n : ℕ) (K : Fin n → Fin n → ℝ) : Prop :=
  ∀ f : Fin n → ℝ, (∀ y, 0 ≤ f y) → (∃ y, 0 < f y) →
    ∀ x, 0 < transfer n K f x

theorem transfer_isPositivityImproving
    (n : ℕ) (K : Fin n → Fin n → ℝ)
    (hK : ∀ x y, 0 < K x y) :
    IsPositivityImproving n K := by
  intro f hf_nonneg hf_nonzero x
  obtain ⟨y₀, hy₀⟩ := hf_nonzero
  have hterm : 0 < K x y₀ * f y₀ := mul_pos (hK x y₀) hy₀
  have hsum : 0 < ∑ y, K x y * f y := by
    apply Finset.sum_pos' (fun y _ => mul_nonneg (le_of_lt (hK x y)) (hf_nonneg y))
    exact ⟨y₀, Finset.mem_univ _, hterm⟩
  exact hsum

end Pphi2Clean.OS
