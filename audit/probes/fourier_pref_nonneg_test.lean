import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open MeasureTheory Pphi2Clean.Continuum
example (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (t : Fin m → ℝ) (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    0 ≤ ((L : ℂ)⁻¹ ^ d * ∑' k : Fin d → ℤ,
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)).re := by
  have hsum := torusFourierSquareTsum_re_nonneg d m L mass hL hmass t fs
  have hpref : (L : ℂ)⁻¹ ^ d = (L⁻¹ ^ d : ℝ) := by simp [Complex.ofReal_inv]
  rw [hpref, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) hsum
