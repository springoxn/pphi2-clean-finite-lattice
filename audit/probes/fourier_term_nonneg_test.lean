import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open MeasureTheory Pphi2Clean.Continuum
example (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (k : Fin d → ℤ) (z : ℂ) :
    0 ≤ (star z * z / (torusMassSymbol d L mass k : ℂ)).re := by
  have hD := torusMassSymbol_pos d L mass hmass k
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_div, mul_zero, add_zero]
  simp [Complex.normSq]
  exact div_nonneg
    (mul_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) hD.le)
    (mul_nonneg hD.le hD.le)
