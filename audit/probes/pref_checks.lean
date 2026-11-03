import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
example (d : ℕ) (L : ℝ) :
    (L : ℂ)⁻¹ ^ d = (L⁻¹ ^ d : ℝ) := by
  simp [Complex.ofReal_inv]
example (d : ℕ) (L : ℝ) (hL : 0 < L) :
    0 < (L⁻¹ ^ d : ℝ) := by positivity
