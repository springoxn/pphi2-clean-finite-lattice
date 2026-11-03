import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
open MeasureTheory Pphi2Clean.Continuum
set_option maxHeartbeats 800000 in
example (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (t : Fin m → ℝ) (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ((L : ℂ)⁻¹ ^ d * ∑' k : Fin d → ℤ,
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)) =
      ∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) * torusFourierGreenPairing d L mass (fs i) (fs j) := by
  let Q : Fin m → Fin m → (Fin d → ℤ) → ℂ := fun i j k =>
    (t i : ℂ) * (t j : ℂ) *
      (star (torusFourierCoefficient d L (fs i) k) *
        torusFourierCoefficient d L (fs j) k /
        (torusMassSymbol d L mass k : ℂ))
  have hsingle (i j : Fin m) : Summable (Q i j) := by
    dsimp [Q]
    have h := torusFourierGreenTerm_summable d L mass hL hmass (fs i) (fs j)
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (h.mul_left (t i : ℂ)).mul_left (t j : ℂ)
  have hinner (i : Fin m) (s : Finset (Fin m)) :
      Summable (fun k => s.sum (fun j => Q i j k)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hsingle i j).add ih
  have hq0 : Summable (fun k => Finset.univ.sum (fun i => Finset.univ.sum (fun j => Q i j k))) := by
    exact torusFourierGreenTerm_quadratic_summable d m L mass hL hmass t fs
  have hswapOuter :
      (∑' k, Finset.univ.sum (fun i => Finset.univ.sum (fun j => Q i j k))) =
        Finset.univ.sum (fun i => ∑' k, Finset.univ.sum (fun j => Q i j k)) := by
    apply Summable.tsum_finsetSum
    intro i hi
    exact hinner i Finset.univ
  have hswapInner (i : Fin m) :
      (∑' k, Finset.univ.sum (fun j => Q i j k)) =
        Finset.univ.sum (fun j => ∑' k, Q i j k) := by
    apply Summable.tsum_finsetSum
    intro j hj
    exact hsingle i j
  simp_rw [← torusFourierGreenTerm_quadratic_eq_square d m L mass t fs]
  change (L : ℂ)⁻¹ ^ d * (∑' k, Finset.univ.sum (fun i => Finset.univ.sum (fun j => Q i j k))) = _
  rw [hswapOuter]
  simp_rw [hswapInner]
  simp only [torusFourierGreenPairing, Q]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [← tsum_mul_left]
  ring_nf
