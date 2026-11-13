import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open Pphi2Clean.Continuum
example (d : ℕ) (L : ℝ) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    star (torusFourierPhase d L k x) = torusFourierPhase d L (-k) x := by
  unfold torusFourierPhase
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I, Finset.sum_neg_distrib]
  left
  simp only [map_ofNat]
  ring
