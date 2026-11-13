import AImathPPhi2Clean.FiniteRealFamilyWeakLimitInterface
open MeasureTheory Pphi2Clean.Continuum
example (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, t i * t j *
      periodicResolventCovarianceMatrix d m L mass hmass fs i j := by
  have hfour := torusFourierGreenPairing_quadratic_eq_square_tsum
    d m L mass hL hmass (fun i => t i) fs
  have hnon := torusFourierSquareTsum_prefactor_re_nonneg
    d m L mass hL hmass (fun i => t i) fs
  have hpair : (∑ i : Fin m, ∑ j : Fin m,
      (t i : ℂ) * (t j : ℂ) *
        physicalTorusResolventPairing d L mass hmass (fs i) (fs j)) =
      ∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) *
          torusFourierGreenPairing d L mass (fs i) (fs j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [torusFourierGreenPairing_eq_physicalTorusResolventPairing
      d L mass hL hmass (fs i) (fs j)]
  calc
    ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        periodicResolventCovarianceMatrix d m L mass hmass fs i j =
      (∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) *
          physicalTorusResolventPairing d L mass hmass (fs i) (fs j)).re := by
            simp [periodicResolventCovarianceMatrix, Complex.mul_re]
    _ = (∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) *
          torusFourierGreenPairing d L mass (fs i) (fs j)).re := by rw [hpair]
    _ = ((L : ℂ)⁻¹ ^ d * ∑' k : Fin d → ℤ,
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)).re := by rw [← hfour]
    _ ≥ 0 := hnon
