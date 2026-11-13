import AImathPPhi2Clean.PeriodicNegativeSobolevCarriers
noncomputable section
namespace Pphi2Clean.Continuum
theorem one_le_norm_int_frequency (k : Fin 2 → ℤ) (hk : k ≠ 0) :
    (1 : ℝ) ≤ ‖k‖ := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  have hmax : max (k 0).natAbs (k 1).natAbs ≠ 0 := by
    intro hz
    apply hk
    funext i
    fin_cases i <;> simp_all
  have hnat : 1 ≤ max (k 0).natAbs (k 1).natAbs :=
    Nat.one_le_iff_ne_zero.mpr hmax
  exact_mod_cast hnat
theorem periodicHMinusThreeWeight_le_periodicHMinusTwoFullWeight
    (k : Fin 2 → ℤ) :
    periodicHMinusThreeWeight k ≤ periodicHMinusTwoFullWeight k := by
  by_cases hk : k = 0
  · simp [periodicHMinusThreeWeight, periodicHMinusTwoFullWeight, hk]
  · rw [periodicHMinusThreeWeight, periodicHMinusTwoFullWeight]
    simp only [hk, ↓reduceIte]
    rw [periodicHMinusTwoWeight]
    simp only [hk, ↓reduceIte]
    apply Real.rpow_le_rpow_of_exponent_le
      (one_le_norm_int_frequency k hk)
    norm_num
theorem periodicHMinusTwoCarrier_in_periodicHMinusThreeCarrier
    {c : (Fin 2 → ℤ) → ℂ}
    (hc : c ∈ periodicHMinusTwoCarrier) :
    c ∈ periodicHMinusThreeCarrier := by
  rw [periodicHMinusTwoCarrier] at hc
  rw [periodicHMinusThreeCarrier]
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (periodicHMinusThreeWeight_nonneg k) (sq_nonneg ‖c k‖))
    (fun k => mul_le_mul_of_nonneg_right
      (periodicHMinusThreeWeight_le_periodicHMinusTwoFullWeight k)
      (sq_nonneg ‖c k‖))
    hc
end Pphi2Clean.Continuum
