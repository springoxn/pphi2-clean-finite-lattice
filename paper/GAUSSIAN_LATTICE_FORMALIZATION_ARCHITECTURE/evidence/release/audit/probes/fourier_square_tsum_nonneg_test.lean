import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open MeasureTheory Pphi2Clean.Continuum
example (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (t : Fin m → ℝ) (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    0 ≤ (∑' k : Fin d → ℤ,
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)).re := by
  have hq0 := torusFourierGreenTerm_quadratic_summable d m L mass hL hmass t fs
  have hq : Summable (fun k : Fin d → ℤ =>
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)) := by
    simpa only [torusFourierGreenTerm_quadratic_eq_square d m L mass t fs] using hq0
  rw [Complex.re_tsum hq]
  apply tsum_nonneg
  intro k
  exact torusFourierSquareTerm_re_nonneg d L mass hmass k _
