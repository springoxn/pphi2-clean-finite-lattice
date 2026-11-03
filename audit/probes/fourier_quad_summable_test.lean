import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open MeasureTheory Pphi2Clean.Continuum
set_option maxHeartbeats 800000 in
example (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (t : Fin m → ℝ) (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Summable (fun k : Fin d → ℤ =>
      ∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) *
          (star (torusFourierCoefficient d L (fs i) k) *
            torusFourierCoefficient d L (fs j) k /
            (torusMassSymbol d L mass k : ℂ))) := by
  let Q : Fin m → Fin m → (Fin d → ℤ) → ℂ := fun i j k =>
    (t i : ℂ) * (t j : ℂ) *
      (star (torusFourierCoefficient d L (fs i) k) *
        torusFourierCoefficient d L (fs j) k /
        (torusMassSymbol d L mass k : ℂ))
  have hsingle (i j : Fin m) : Summable (Q i j) := by
    dsimp [Q]
    have h := torusFourierGreenTerm_summable d L mass hL hmass (fs i) (fs j)
    simpa [mul_assoc, mul_comm, mul_left_comm] using (h.mul_left (t i : ℂ)).mul_left (t j : ℂ)
  have hinner (i : Fin m) (s : Finset (Fin m)) : Summable (fun k => s.sum (fun j => Q i j k)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hsingle i j).add ih
  have houter (s : Finset (Fin m)) : Summable (fun k => s.sum (fun i => Finset.univ.sum (fun j => Q i j k))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hinner i Finset.univ).add ih
  simpa [Q] using houter (Finset.univ : Finset (Fin m))
