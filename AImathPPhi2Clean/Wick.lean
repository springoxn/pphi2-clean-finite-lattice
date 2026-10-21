import Mathlib

/-!
# L0-1 -- finite-dimensional Wick powers :X^n:  (paper S1.1 / lemma [L27])

Paper source: proofs/pphi2_global_proof.md S1.1, lemmas/README.md [L27]/[L28].
Roadmap: formal/lean/pphi2_formalization_plan.md Level 0.

For a mean-zero Gaussian X with variance c = sigma^2, the Wick power is

    :e^{aX}: = exp(aX - a^2 c / 2),      :X^n: := (d/da)^n :e^{aX}: at a = 0 .

We define `wick c n` by the equivalent Hermite three-term recurrence

    W_0 = 1 ,   W_1 = X ,   W_{n+2} = X * W_{n+1} - (n+1) * c * W_n ,

which is the a = 0 restriction of the ODE  d/da :e^{aX}: = (X - a*c) * :e^{aX}: .
Taking the recurrence as the definition keeps every downstream identity algebraic
(a lemma about Polynomial Real), with no analysis and no measure theory.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace Wick

/-- The Wick power :X^n: as a polynomial in X, variance parameter c = sigma^2.
Defined by the Hermite recurrence (see the module docstring). -/
noncomputable def wick (c : Real) : Nat -> Polynomial Real
  | 0 => 1
  | 1 => X
  | (n + 2) => X * wick c (n + 1) - C (((n + 1 : Nat) : Real) * c) * wick c n

@[simp] theorem wick_zero (c : Real) : wick c 0 = 1 := rfl

@[simp] theorem wick_one (c : Real) : wick c 1 = X := rfl

/-- The defining recurrence, in n+2 form. -/
theorem wick_add_two (c : Real) (n : Nat) :
    wick c (n + 2) = X * wick c (n + 1) - C (((n + 1 : Nat) : Real) * c) * wick c n := rfl

/-! ### Displayed cases of paper (1.3)

Paper lists :X^0: = 1, :X^1: = X, :X^2: = X^2 - c, :X^3: = X^3 - 3*c*X,
:X^4: = X^4 - 6*c*X^2 + 3*c^2.  Here c plays the role of sigma^2. -/

theorem wick_two (c : Real) : wick c 2 = X ^ 2 - C c := by
  rw [show wick c 2 = X * wick c 1 - C (((0 + 1 : Nat) : Real) * c) * wick c 0
        from wick_add_two c 0]
  rw [wick_one, wick_zero]
  simp
  ring_nf

theorem wick_three (c : Real) : wick c 3 = X ^ 3 - C (3 * c) * X := by
  rw [show wick c 3 = X * wick c 2 - C (((1 + 1 : Nat) : Real) * c) * wick c 1
        from wick_add_two c 1]
  rw [wick_two, wick_one]
  simp
  simp only [C_ofNat]
  ring

theorem wick_four (c : Real) : wick c 4 = X ^ 4 - C (6 * c) * X ^ 2 + C (3 * c ^ 2) := by
  rw [show wick c 4 = X * wick c 3 - C (((2 + 1 : Nat) : Real) * c) * wick c 2
        from wick_add_two c 2]
  rw [wick_three, wick_two]
  simp
  simp only [C_ofNat]
  ring

/-! ### Degree bound -/

theorem natDegree_wick_le (c : Real) (n : Nat) : (wick c n).natDegree <= n :=
  Nat.strong_induction_on n (fun n ih => by
    match n with
    | 0 => simp
    | 1 => simp
    | (m + 2) =>
      rw [wick_add_two]
      have h1 : (X * wick c (m + 1)).natDegree <= m + 2 := by
        calc (X * wick c (m + 1)).natDegree
            <= X.natDegree + (wick c (m + 1)).natDegree := natDegree_mul_le
          _ <= 1 + (m + 1) := add_le_add (le_of_eq natDegree_X) (ih (m + 1) (by omega))
          _ = m + 2 := by ring
      have h2 : (C (((m + 1 : Nat) : Real) * c) * wick c m).natDegree <= m + 2 := by
        calc (C (((m + 1 : Nat) : Real) * c) * wick c m).natDegree
            <= (C (((m + 1 : Nat) : Real) * c)).natDegree + (wick c m).natDegree := natDegree_mul_le
          _ <= 0 + m := add_le_add (le_of_eq (natDegree_C _)) (ih m (by omega))
          _ <= m + 2 := by omega
      exact le_trans (natDegree_sub_le _ _) (max_le h1 h2))

end Wick
