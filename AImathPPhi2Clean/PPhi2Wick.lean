import Mathlib

noncomputable section

namespace Pphi2Clean

/-- Scalar Wick monomials, matching the upstream Pphi2 recurrence. -/
def wickMonomial : Nat → Real → Real → Real
  | 0, _, _ => 1
  | 1, _, x => x
  | n + 2, c, x => x * wickMonomial (n + 1) c x - (n + 1 : Real) * c * wickMonomial n c x

@[simp] theorem wickMonomial_zero (c x : Real) : wickMonomial 0 c x = 1 := rfl

@[simp] theorem wickMonomial_one (c x : Real) : wickMonomial 1 c x = x := rfl

theorem wickMonomial_succ_succ (n : Nat) (c x : Real) :
    wickMonomial (n + 2) c x =
      x * wickMonomial (n + 1) c x - (n + 1 : Real) * c * wickMonomial n c x := rfl

theorem wickMonomial_four (c x : Real) :
    wickMonomial 4 c x = x ^ 4 - 6 * c * x ^ 2 + 3 * c ^ 2 := by
  simp [wickMonomial_succ_succ]
  ring

end Pphi2Clean
