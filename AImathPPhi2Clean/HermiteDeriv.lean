import Mathlib

/-!
# Hermite derivative -- a Mathlib gap closed (prerequisite for L0-2)

Mathlib's Polynomial.hermite (the probabilists Hermite polynomials He_n) is defined by
hermite (n+1) = X * hermite n - derivative (hermite n), but Mathlib does NOT provide the
resulting three-term recurrence in derivative form
derivative (hermite (n+1)) = (n+1) . hermite n  (equivalently He_{n+1} = (n+1) He_n),
which is what the Wick <-> Hermite bridge needs.

Proof: compare coefficients via Polynomial.coeff_hermite (explicit closed form); the whole
content reduces to the binomial identity (k+1) * (n+1).choose (k+1) = (n+1) * n.choose k,
which follows from Nat.choose_succ_right_eq and Nat.choose_mul_succ_eq.

Paper source: proofs/pphi2_global_proof.md S1.1 (probabilists convention, eq. (1.2));
roadmap formal/lean/pphi2_formalization_plan.md L0-2 route (c).
-/

open Polynomial

namespace HermiteDeriv

/-- Binomial identity (k+1) * C(n+1,k+1) = (n+1) * C(n,k). -/
theorem nat_mul_choose_succ_succ (n k : Nat) :
    (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
  rw [mul_comm (k+1), Nat.choose_succ_right_eq (n+1) k, ← Nat.choose_mul_succ_eq n k, mul_comm]

end HermiteDeriv

namespace Polynomial

/-- **Mathlib gap closed**: the derivative of the probabilists Hermite polynomial is
He_{n+1} = (n+1) He_n, i.e. derivative (hermite (n+1)) = (n+1) . hermite n. -/
theorem derivative_hermite (n : Nat) :
    derivative (hermite (n + 1)) = C ((n + 1 : Int)) * hermite n := by
  ext k
  rw [coeff_derivative, coeff_C_mul, coeff_hermite, coeff_hermite]
  rw [show n + 1 + (k + 1) = n + k + 2 by omega]
  rw [show n + 1 - (k + 1) = n - k by omega]
  have he : Even (n + k + 2) ↔ Even (n + k) := by
    rw [show n + k + 2 = (n + k) + 2 by omega, Nat.even_add]
    simp
  simp only [he]
  split_ifs with h
  · have hci : (((n + 1).choose (k + 1) : Nat) : Int) * ((k + 1 : Nat) : Int)
        = ((n + 1 : Nat) : Int) * ((n.choose k : Nat) : Int) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, mul_comm]
      norm_cast
      exact HermiteDeriv.nat_mul_choose_succ_succ n k
    rw [show ((k : Int) + 1) = ((k + 1 : Nat) : Int) by push_cast; ring]
    rw [show (-1 : Int) ^ ((n - k) / 2) * ↑(n - k - 1).doubleFactorial * ↑((n + 1).choose (k + 1)) * ↑(k + 1)
          = ((-1 : Int) ^ ((n - k) / 2) * ↑(n - k - 1).doubleFactorial) * (↑((n + 1).choose (k + 1)) * ↑(k + 1))
          from by ring]
    rw [hci]
    rw [show ((n + 1 : Nat) : Int) = ((n : Int) + 1) from by push_cast; ring]
    ring
  · ring

end Polynomial
