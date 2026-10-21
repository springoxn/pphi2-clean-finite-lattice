import AImathPPhi2Clean.Wick
import AImathPPhi2Clean.HermiteDeriv

/-!
# Wick <-> Hermite bridge (L0-2 route (c))

wick (s^2) n = C (s^n) * (H n).comp (C (1/s) * X)   for s != 0,
where H n is Mathlibs probabilists Hermite polynomial pushed to Real.
Uses Polynomial.derivative_hermite (S6Isserlis/HermiteDeriv.lean).
-/

open Polynomial

noncomputable section

namespace WickBridge

def H (n : Nat) : Polynomial Real := (hermite n).map (Int.castRingHom Real)

def qs (s : Real) : Polynomial Real := C (1/s) * X

@[simp] lemma H_zero : H 0 = 1 := by simp [H]

@[simp] lemma H_one : H 1 = X := by simp [H]

lemma H_succ (n : Nat) : H (n+1) = X * H n - derivative (H n) := by
  simp [H, hermite_succ, derivative_map]

lemma deriv_H (n : Nat) : derivative (H (n+1)) = C ((n : Real) + 1) * H n := by
  unfold H
  rw [derivative_map, Polynomial.derivative_hermite]
  simp [map_mul, map_C, map_intCast]

theorem wick_eq_hermite (s : Real) (hs : s ≠ 0) (n : Nat) :
    Wick.wick (s^2) n = C (s^n) * (H n).comp (qs s) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Wick.wick_zero, H, qs]
  | one =>
      rw [Wick.wick_one, H_one, qs]
      simp only [pow_one, mul_comp, X_comp, C_comp]
      rw [← mul_assoc, ← C_mul, one_div, mul_inv_cancel₀ hs, C_1, one_mul]
  | more n ih0 ih1 =>
      have hHs : H (n+2) = X * H (n+1) - C ((n : Real) + 1) * H n := by
        rw [show n + 2 = (n + 1) + 1 by omega, H_succ (n + 1), deriv_H n]
      have hp : s ^ (n + 2) * (1 / s) = s ^ (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, one_div, mul_assoc,
            mul_inv_cancel₀ hs, mul_one]
      have hs2 : s ^ (n + 2) = s ^ 2 * s ^ n := by
        rw [show n + 2 = 2 + n by omega, pow_add]
      rw [Wick.wick_add_two, ih1, ih0, hHs]
      simp only [sub_comp, mul_comp, C_comp, X_comp, qs]
      rw [show (((n + 1 : Nat)) : Real) = ((n : Real) + 1) by push_cast; ring]
      simp only [mul_sub, mul_assoc]
      simp only [← mul_assoc, ← C_mul]
      rw [hp, hs2]
      ring

end WickBridge
