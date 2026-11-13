import AImathPPhi2Clean.FiniteRealFamilyWeakLimitInterface
open Pphi2Clean.Continuum
example {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hquad : ∀ t : EuclideanSpace ℝ (Fin m),
      0 ≤ ∑ i : Fin m, ∑ j : Fin m, t i * t j * M i j) :
    M.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · show M.conjTranspose = M
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact hsym j i
  · intro x
    let t : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x
    have h := hquad t
    simpa [dotProduct, Matrix.mulVec, t, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm] using h
