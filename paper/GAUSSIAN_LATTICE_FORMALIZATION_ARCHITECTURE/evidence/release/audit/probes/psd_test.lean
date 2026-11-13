import AImathPPhi2Clean.FiniteRealFamilyWeakLimitInterface
open Pphi2Clean.Continuum
example {m : ℕ} (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (t : EuclideanSpace ℝ (Fin m)) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, t i * t j *
      @inner ℝ (EuclideanSpace ℝ (Fin m)) _
        (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) := by
  let v : EuclideanSpace ℝ (Fin m) :=
    ∑ i : Fin m, t i • T (targetCoordinateFamily m i)
  have hv : @inner ℝ (EuclideanSpace ℝ (Fin m)) _ v v =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        @inner ℝ (EuclideanSpace ℝ (Fin m)) _
          (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) := by
    simp only [v, real_inner_comm, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [← hv, real_inner_self_eq_norm_sq]
  exact sq_nonneg _
