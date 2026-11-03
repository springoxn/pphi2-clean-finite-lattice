import S6Isserlis.S1a

/-!
# S4 — Algebraic OS0 symmetry core

These theorems cover only exchange symmetry, common translation invariance,
and invariance under linear isometries.  Positivity and off-diagonal
smoothness require separate integral-analysis results.
-/

noncomputable section

namespace Schwinger

/-- Exchange symmetry of the radial two-point definition. -/
theorem s4_symmetric (m : ℝ) (x y : Fin 4 → ℝ) :
    twoPoint m x y = twoPoint m y x := by
  unfold twoPoint
  rw [norm_sub_rev]

/-- Invariance under a common translation. -/
theorem s4_translation_invariant (m : ℝ) (x y v : Fin 4 → ℝ) :
    twoPoint m (x + v) (y + v) = twoPoint m x y := by
  unfold twoPoint
  congr 2
  congr 1
  funext i
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Invariance under a linear isometry of the finite-dimensional Euclidean space. -/
theorem s4_orthogonal_invariant (m : ℝ)
    (Q : LinearIsometryEquiv (RingHom.id ℝ) (Fin 4 → ℝ) (Fin 4 → ℝ))
    (x y : Fin 4 → ℝ) :
    twoPoint m (Q x) (Q y) = twoPoint m x y := by
  unfold twoPoint
  have hsub : Q x - Q y = Q (x - y) := by
    rw [Q.map_sub]
  rw [hsub, Q.norm_map]

end Schwinger
