import AImathPPhi2Clean.PeriodicFourierLaplacian

noncomputable section
namespace Pphi2Clean.Continuum

/-- The signed integer box embeds in the periodic frequency ball once N>2K. -/
def frequencyBoxMode (N K : ℕ) (q : Fin (2 * K + 1)) : ZMod N :=
  ((q.val : ℤ) - (K : ℤ) : ℤ)

theorem frequencyBoxMode_injective (N K : ℕ) [NeZero N] (hN : 2 * K < N) :
    Function.Injective (frequencyBoxMode N K) := by
  intro q r h
  have he : (q.val : ZMod N) = (r.val : ZMod N) := by
    simpa [frequencyBoxMode, sub_eq_sub_iff_add_eq_add] using h
  have hq : q.val < N := by omega
  have hr : r.val < N := by omega
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hq, ZMod.val_natCast_of_lt hr] at hv
  exact Fin.ext hv

theorem frequencyBoxMode_mem (N K : ℕ) [NeZero N] (hN : 2 * K < N)
    (q : Fin (2 * K + 1)) :
    min (frequencyBoxMode N K q).val (N - (frequencyBoxMode N K q).val) ≤ K := by
  by_cases hq : K ≤ q.val
  · have he : frequencyBoxMode N K q = ((q.val - K : ℕ) : ZMod N) := by
      simp only [frequencyBoxMode, Nat.cast_sub hq, Int.cast_sub, Int.cast_natCast]
    rw [he, ZMod.val_natCast_of_lt (show q.val - K < N by omega)]
    exact le_trans (min_le_left _ _) (by omega)
  · have hlt : q.val < K := by omega
    have he : frequencyBoxMode N K q = -((K - q.val : ℕ) : ZMod N) := by
      simp only [frequencyBoxMode, Nat.cast_sub hlt.le, Int.cast_sub, Int.cast_natCast]
      ring
    have hv : (((K - q.val : ℕ) : ZMod N)).val = K - q.val :=
      ZMod.val_natCast_of_lt (by omega)
    have hz : ((K - q.val : ℕ) : ZMod N) ≠ 0 := by
      intro hh
      have hh' := congrArg ZMod.val hh
      simp only [hv, ZMod.val_zero] at hh'
      omega
    letI : NeZero (((K - q.val : ℕ) : ZMod N)) := ⟨hz⟩
    rw [he, ZMod.val_neg_of_ne_zero, hv]
    exact le_trans (min_le_right _ _) (by omega)

theorem frequencyBoxMode_surjective (N K : ℕ) [NeZero N] (hN : 2 * K < N)
    (p : ZMod N) (hp : min p.val (N - p.val) ≤ K) :
    ∃ q : Fin (2 * K + 1), frequencyBoxMode N K q = p := by
  have hv := ZMod.val_lt p
  by_cases hlow : p.val ≤ K
  · refine ⟨⟨p.val + K, by omega⟩, ?_⟩
    simp [frequencyBoxMode, ZMod.natCast_zmod_val]
  · have hhigh : N - p.val ≤ K := by omega
    refine ⟨⟨K - (N - p.val), by omega⟩, ?_⟩
    have he : ((K - (N - p.val) : ℕ) : ℤ) - (K : ℤ) =
        (p.val : ℤ) - (N : ℤ) := by omega
    simp only [frequencyBoxMode, he, Int.cast_sub, Int.cast_natCast,
      ZMod.natCast_zmod_val, ZMod.natCast_self, sub_zero]

/-- Exact reindexing of the periodic cutoff by a signed integer box. -/
theorem periodicFrequencyBox_sum
    (d N K : ℕ) [NeZero N] (hN : 2 * K < N)
    (F : (Fin d → ZMod N) → ℂ) :
    (∑ p : Fin d → ZMod N,
      if (∀ i, min (p i).val (N - (p i).val) ≤ K) then F p else 0) =
    ∑ q : Fin d → Fin (2 * K + 1),
      F (fun i => (((q i).val : ℤ) - (K : ℤ) : ℤ)) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun q _ => fun i => frequencyBoxMode N K (q i))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun i => frequencyBoxMode_mem N K hN (q i)
  · intro q hq r hr he
    funext i
    exact frequencyBoxMode_injective N K hN (congrFun he i)
  · intro p hp
    have hp' : ∀ i, min (p i).val (N - (p i).val) ≤ K := (Finset.mem_filter.mp hp).2
    choose q hq using fun i => frequencyBoxMode_surjective N K hN (p i) (hp' i)
    exact ⟨q, Finset.mem_univ _, funext hq⟩
  · intro q hq
    rfl

end Pphi2Clean.Continuum
