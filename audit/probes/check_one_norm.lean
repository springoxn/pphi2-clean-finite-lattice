import AImathPPhi2Clean.PeriodicHMinusTwoWeight
open Pphi2Clean.Continuum
example (k : Fin 2 → ℤ) (hk : k ≠ 0) : (1 : ℝ) ≤ ‖k‖ := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  have h : ∃ i, k i ≠ 0 := by
    by_contra h
    apply hk
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := h
  have hi1 : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
  rw [max_def]
  split_ifs with hmax
  · exact hi1
  · exact le_max_of_le_right hi1
