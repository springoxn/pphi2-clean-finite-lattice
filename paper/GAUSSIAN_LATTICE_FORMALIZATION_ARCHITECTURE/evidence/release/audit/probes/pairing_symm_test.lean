import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open MeasureTheory Pphi2Clean.Continuum
example (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    torusFourierGreenPairing d L mass f g =
      torusFourierGreenPairing d L mass g f := by
  unfold torusFourierGreenPairing
  congr 1
  rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq]
  congr 1
  funext k
  simp only [Equiv.neg_apply]
  rw [torusFourierCoefficient_star_eq_neg,
    torusFourierCoefficient_star_eq_neg]
  have hmassneg : torusMassSymbol d L mass (-k) = torusMassSymbol d L mass k := by
    simp [torusMassSymbol]
  rw [hmassneg, neg_neg, mul_comm]
