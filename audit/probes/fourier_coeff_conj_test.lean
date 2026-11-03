import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open MeasureTheory Pphi2Clean.Continuum
example (d : ℕ) (L : ℝ) (f : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (k : Fin d → ℤ) :
    star (torusFourierCoefficient d L f k) =
      torusFourierCoefficient d L f (-k) := by
  unfold torusFourierCoefficient
  change (starRingEnd ℂ) (∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) L),
      (f x : ℂ) * torusFourierPhase d L (-k) x) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, Complex.conj_ofReal]
  change (f x : ℂ) * star (torusFourierPhase d L (-k) x) =
    (f x : ℂ) * torusFourierPhase d L (-(-k)) x
  rw [torusFourierPhase_star_eq_neg]
