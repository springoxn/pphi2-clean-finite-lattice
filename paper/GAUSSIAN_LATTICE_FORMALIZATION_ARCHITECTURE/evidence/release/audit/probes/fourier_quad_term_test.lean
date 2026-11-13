import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open MeasureTheory Pphi2Clean.Continuum
example (d m : ℕ) (L mass : ℝ) (t : Fin m → ℝ)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (k : Fin d → ℤ) :
    (∑ i : Fin m, ∑ j : Fin m,
      (t i : ℂ) * (t j : ℂ) *
        (star (torusFourierCoefficient d L (fs i) k) *
          torusFourierCoefficient d L (fs j) k /
          (torusMassSymbol d L mass k : ℂ))) =
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ) := by
  simp [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, Complex.star_def, Complex.conj_ofReal]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
