import AImathPPhi2Clean.FiniteRealFamilyWeakLimitInterface
open MeasureTheory Pphi2Clean.Continuum
example (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Matrix.PosSemidef (periodicResolventCovarianceMatrix d m L mass hmass fs) := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · show Matrix.conjTranspose (periodicResolventCovarianceMatrix d m L mass hmass fs :
        Matrix (Fin m) (Fin m) ℝ) =
      (periodicResolventCovarianceMatrix d m L mass hmass fs : Matrix (Fin m) (Fin m) ℝ)
    ext i j
    change star (periodicResolventCovarianceMatrix d m L mass hmass fs j i) =
      periodicResolventCovarianceMatrix d m L mass hmass fs i j
    simp only [star_trivial]
    exact periodicResolventCovarianceMatrix_symmetric_of_fourier d m L mass hL hmass fs j i
  · intro x
    let t : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x
    have h := periodicResolventCovarianceMatrix_nonneg_quadratic_of_fourier
      d m L mass hL hmass fs t
    simpa [dotProduct, Matrix.mulVec, t, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm] using h
