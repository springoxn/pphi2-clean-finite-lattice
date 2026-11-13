/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from GaussianField/Tightness.lean, summable_coeff_mul_pow.
-/
import Mathlib

noncomputable section
namespace Pphi2Clean.Continuum

/-- The inverse-square majorant is summable, independently of coefficient data. -/
theorem inverseSquare_summable :
    Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
  exact ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
    Nat.succ_injective).congr (fun n => by simp [Nat.succ_eq_add_one]; ring)

/-- Two powers of extra coefficient decay absorb a polynomial coordinate bound. -/
theorem weighted_coefficient_le (a : ℕ → ℝ) (r : ℕ) (A : ℝ)
    (hdecay : ∀ n, |a n| * (1 + (n : ℝ)) ^ (r + 2) ≤ A) (n : ℕ) :
    |a n| * (1 + (n : ℝ)) ^ r ≤ A * (1 / (1 + (n : ℝ)) ^ 2) := by
  calc
    |a n| * (1 + (n : ℝ)) ^ r =
        (|a n| * (1 + (n : ℝ)) ^ (r + 2)) / (1 + (n : ℝ)) ^ 2 := by
      rw [pow_add]
      field_simp
    _ ≤ A / (1 + (n : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_right (hdecay n) (by positivity)
    _ = A * (1 / (1 + (n : ℝ)) ^ 2) := by ring

/-- Absolute summability of polynomially weighted coefficients. -/
theorem weighted_coefficients_summable (a : ℕ → ℝ) (r : ℕ) (A : ℝ)
    (hdecay : ∀ n, |a n| * (1 + (n : ℝ)) ^ (r + 2) ≤ A) :
    Summable (fun n => |a n| * (1 + (n : ℝ)) ^ r) := by
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (by positivity))
    (weighted_coefficient_le a r A hdecay) (inverseSquare_summable.mul_left A)

/-- The weighted coefficient series has an explicit finite majorant. -/
theorem weighted_coefficients_tsum_le (a : ℕ → ℝ) (r : ℕ) (A : ℝ)
    (hdecay : ∀ n, |a n| * (1 + (n : ℝ)) ^ (r + 2) ≤ A) :
    (∑' n, |a n| * (1 + (n : ℝ)) ^ r) ≤
      A * ∑' n : ℕ, 1 / (1 + (n : ℝ)) ^ 2 := by
  calc
    _ ≤ ∑' n : ℕ, A * (1 / (1 + (n : ℝ)) ^ 2) :=
      (weighted_coefficients_summable a r A hdecay).tsum_le_tsum
        (weighted_coefficient_le a r A hdecay) (inverseSquare_summable.mul_left A)
    _ = _ := tsum_mul_left

end Pphi2Clean.Continuum
