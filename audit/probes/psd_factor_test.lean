import AImathPPhi2Clean.FiniteRealFamilyWeakLimitInterface
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice
open Pphi2Clean.Continuum
open scoped MatrixOrder
noncomputable section

example (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : Matrix.PosSemidef A) :
    ∃ T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m),
      ∀ i j, @inner ℝ (EuclideanSpace ℝ (Fin m)) _
        (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) = A i j := by
  let B : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt A
  have hBsq : B * B = A := by
    simpa [B, pow_two] using (CFC.sq_sqrt A hA.nonneg)
  have hBherm : B.IsHermitian := by
    simpa [B] using (CFC.sqrt_nonneg A).1
  let M : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.mk (Matrix.mulVecLin B)
      (LinearMap.continuous_of_finiteDimensional (Matrix.mulVecLin B))
  let T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp M
  refine ⟨T, ?_⟩
  intro i j
  change inner ℝ (WithLp.toLp 2 (B.mulVec (Pi.single i 1)))
    (WithLp.toLp 2 (B.mulVec (Pi.single j 1))) = A i j
  rw [B.mulVec_single_one, B.mulVec_single_one]
  simp only [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply]
  simp only [Matrix.col_apply, starRingEnd_apply, star_trivial]
  calc
    (∑ x, B x j * B x i) = ∑ x, B i x * B x j := by
      apply Finset.sum_congr rfl
      intro x hx
      have hsym := congrFun (congrFun hBherm i) x
      simp only [Matrix.conjTranspose_apply, star_trivial] at hsym
      rw [hsym]
      ring
    _ = (B * B) i j := by rw [Matrix.mul_apply]
    _ = A i j := congrFun (congrFun hBsq i) j
