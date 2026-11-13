import AImathPPhi2Clean.PeriodicNegativeSobolevCarriers
open Pphi2Clean.Continuum
example (k : Fin 2 → ℤ) (hk : k ≠ 0) : (1 : ℝ) ≤ ‖k‖ := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  have hmax : max (k 0).natAbs (k 1).natAbs ≠ 0 := by
    intro hz
    apply hk
    funext i
    fin_cases i <;> simp_all
  have hnat : 1 ≤ max (k 0).natAbs (k 1).natAbs := Nat.one_le_iff_ne_zero.mpr hmax
  exact_mod_cast hnat
