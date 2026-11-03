import Mathlib

/-!
# S1a — Schwinger-parameter definition layer

This module formalizes only the definition-level A representation.  The
modified-Bessel closed form and convergence analysis are separate claims.
-/

noncomputable section

open scoped Interval

namespace Schwinger

/-- Schwinger parameter integral used as the definition-level kernel object. -/
def aIntegral (m r : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    t⁻¹ ^ 2 * Real.exp (-(m ^ 2 * t) - r ^ 2 / (4 * t))

/-- Definition-level Euclidean two-point kernel. -/
def twoPoint (m : ℝ) (x y : Fin 4 → ℝ) : ℝ :=
  (1 / (16 * Real.pi ^ 2)) * aIntegral m ‖x - y‖

/-- S1a: the two-point kernel is defined by the Schwinger parameter integral. -/
theorem s1a_definitional (m : ℝ) (x y : Fin 4 → ℝ) :
    twoPoint m x y =
      (1 / (16 * Real.pi ^ 2)) * aIntegral m ‖x - y‖ := by
  rfl

end Schwinger
