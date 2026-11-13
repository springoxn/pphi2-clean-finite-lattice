import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
example (m : ℕ) (i0 : Fin m) (u v : Fin m → ℂ) :
    (∑ i : Fin m, u i) * v i0 = ∑ i : Fin m, u i * v i0 := by
  rw [Finset.sum_mul]
