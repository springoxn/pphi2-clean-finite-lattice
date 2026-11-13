import AImathPPhi2Clean.PeriodicFourierCovarianceLimit

noncomputable section
open scoped Topology
namespace Pphi2Clean.Continuum

/-- A coordinate outside the integer box has magnitude at least K+1.
The premise is impossible in dimension zero, so no dimension exception is needed. -/
theorem torusMassSymbol_ge_outside_box
    (d : ℕ) (L mass : ℝ) (k : Fin d → ℤ) (K : ℕ)
    (hk : k ∉ torusIntegerFrequencyBox d K) :
    mass ^ 2 + (2 * Real.pi / L) ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2 ≤
      torusMassSymbol d L mass k := by
  classical
  have hx : ∃ i, ¬ (-(K : ℤ) ≤ k i ∧ k i ≤ (K : ℤ)) :=
    not_forall.mp ((torusIntegerFrequencyBox_mem_iff d K k).not.mp hk)
  obtain ⟨i, hi⟩ := hx
  have hs : ((K + 1 : ℕ) : ℝ) ^ 2 ≤ (k i : ℝ) ^ 2 := by
    by_cases hlo : -(K : ℤ) ≤ k i
    · have hip : (K : ℤ) < k i := lt_of_not_ge (fun h => hi ⟨hlo, h⟩)
      have hz : ((K + 1 : ℕ) : ℤ) ≤ k i := by omega
      have hr : ((K + 1 : ℕ) : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hz
      nlinarith [show (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) by positivity]
    · have hin : k i < -(K : ℤ) := lt_of_not_ge hlo
      have hz : k i ≤ -((K + 1 : ℕ) : ℤ) := by omega
      have hr : (k i : ℝ) ≤ -((K + 1 : ℕ) : ℝ) := by exact_mod_cast hz
      nlinarith [show (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) by positivity]
  have hsum : (k i : ℝ) ^ 2 ≤ ∑ j : Fin d, (k j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin d => (k j : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hm := mul_le_mul_of_nonneg_left (hs.trans hsum) (sq_nonneg (2 * Real.pi / L))
  unfold torusMassSymbol
  linarith only [hm]

/-- Every finite subset of a frequency box obeys the same product-energy
bound. This follows from the proved discrete-to-continuum finite Bessel bound. -/
theorem torusFourierCoefficient_norm_product_sum_le_of_subset_box
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (J : ℕ) (s : Finset (Fin d → ℤ)) (hs : s ⊆ torusIntegerFrequencyBox d J) :
    (∑ k ∈ s, ‖torusFourierCoefficient d L f k‖ *
      ‖torusFourierCoefficient d L g k‖) ≤ L ^ (2 * d) * ‖f‖ * ‖g‖ := by
  have energy (u : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
      (∑ k ∈ s, ‖torusFourierCoefficient d L u k‖ ^ 2) ≤ L ^ (2 * d) * ‖u‖ ^ 2 := by
    calc
      _ ≤ ∑ k ∈ torusIntegerFrequencyBox d J, ‖torusFourierCoefficient d L u k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
      _ = ∑ q : Fin d → Fin (2 * J + 1),
          ‖torusFourierCoefficient d L u (torusIntegerFrequencyMode d J q)‖ ^ 2 :=
        torusIntegerFrequencyBox_sum_eq d J _
      _ ≤ _ := torusFourierCoefficient_norm_sq_box_sum_le d L hL u J
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun k => ‖torusFourierCoefficient d L f k‖)
    (fun k => ‖torusFourierCoefficient d L g k‖)
  have hfg := mul_le_mul (energy f) (energy g)
    (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (by positivity)
  have hsq := hcs.trans hfg
  have heq : (L ^ (2 * d) * ‖f‖ ^ 2) * (L ^ (2 * d) * ‖g‖ ^ 2) =
      (L ^ (2 * d) * ‖f‖ * ‖g‖) ^ 2 := by ring
  rw [heq] at hsq
  have hnon : 0 ≤ L ^ (2 * d) * ‖f‖ * ‖g‖ := by positivity
  have hsum : 0 ≤ ∑ k ∈ s, ‖torusFourierCoefficient d L f k‖ *
      ‖torusFourierCoefficient d L g k‖ :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith

/-- Quantitative annulus bound with the exact first omitted integer radius. -/
theorem torusFourierGreenCutoff_sub_cutoff_norm_le
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (K J : ℕ) (hKJ : K ≤ J) :
    ‖torusFourierGreenCutoff d L mass f g J -
      torusFourierGreenCutoff d L mass f g K‖ ≤
      L ^ d * ‖f‖ * ‖g‖ /
        (mass ^ 2 + (2 * Real.pi / L) ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2) := by
  classical
  let R : ℝ := mass ^ 2 + (2 * Real.pi / L) ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  let s := torusIntegerFrequencyBox d J \ torusIntegerFrequencyBox d K
  let t : (Fin d → ℤ) → ℂ := fun k =>
    star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
      (torusMassSymbol d L mass k : ℂ)
  have hterm (k : Fin d → ℤ) (hk : k ∈ s) :
      ‖t k‖ ≤ (‖torusFourierCoefficient d L f k‖ *
        ‖torusFourierCoefficient d L g k‖) / R := by
    have hout : k ∉ torusIntegerFrequencyBox d K := (Finset.mem_sdiff.mp hk).2
    have hD := torusMassSymbol_pos d L mass hmass k
    have hlo := torusMassSymbol_ge_outside_box d L mass k K hout
    dsimp [t]
    rw [norm_div, norm_mul]
    simp only [Complex.star_def, Complex.norm_conj, Complex.norm_of_nonneg hD.le]
    exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hR hlo
  have hsum : ‖∑ k ∈ s, t k‖ ≤ (L ^ (2 * d) * ‖f‖ * ‖g‖) / R := by
    calc
      _ ≤ ∑ k ∈ s, ‖t k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ s, (‖torusFourierCoefficient d L f k‖ *
          ‖torusFourierCoefficient d L g k‖) / R := Finset.sum_le_sum hterm
      _ = (∑ k ∈ s, ‖torusFourierCoefficient d L f k‖ *
          ‖torusFourierCoefficient d L g k‖) / R := by rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right
        (torusFourierCoefficient_norm_product_sum_le_of_subset_box d L hL f g J s
          Finset.sdiff_subset) hR.le
  have hsub := torusIntegerFrequencyBox_mono d hKJ
  have hdiff : (∑ k ∈ torusIntegerFrequencyBox d J, t k) -
      (∑ k ∈ torusIntegerFrequencyBox d K, t k) = ∑ k ∈ s, t k :=
    (Finset.sum_sdiff_eq_sub hsub).symm
  have hnorm : ‖(L : ℂ)⁻¹ ^ d‖ = L⁻¹ ^ d := by
    simp [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  rw [torusFourierGreenCutoff_eq_box_sum, torusFourierGreenCutoff_eq_box_sum]
  change ‖(L : ℂ)⁻¹ ^ d * (∑ k ∈ torusIntegerFrequencyBox d J, t k) -
    (L : ℂ)⁻¹ ^ d * (∑ k ∈ torusIntegerFrequencyBox d K, t k)‖ ≤ _
  rw [← mul_sub, hdiff, norm_mul, hnorm]
  calc
    _ ≤ L⁻¹ ^ d * ((L ^ (2 * d) * ‖f‖ * ‖g‖) / R) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [show L ^ (2 * d) = L ^ d * L ^ d by rw [two_mul, pow_add]]
      have hcancel : L⁻¹ ^ d * L ^ d = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]
      calc
        _ = (L⁻¹ ^ d * L ^ d) * (L ^ d * ‖f‖ * ‖g‖ / R) := by ring
        _ = _ := by rw [hcancel, one_mul]

/-- Explicit continuum Green tail, uniform over all tests with prescribed
supremum norms. The first omitted radius is K+1, including K=0. -/
theorem torusFourierGreenPairing_sub_cutoff_norm_le
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) :
    ‖torusFourierGreenPairing d L mass f g -
      torusFourierGreenCutoff d L mass f g K‖ ≤
      L ^ d * ‖f‖ * ‖g‖ /
        (mass ^ 2 + (2 * Real.pi / L) ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2) := by
  have ht := ((torusFourierGreenCutoff_tendsto d L mass hL hmass f g).sub_const
    (torusFourierGreenCutoff d L mass f g K)).norm
  have hb : ∀ᶠ J : ℕ in Filter.atTop,
      ‖torusFourierGreenCutoff d L mass f g J -
        torusFourierGreenCutoff d L mass f g K‖ ≤
        L ^ d * ‖f‖ * ‖g‖ /
          (mass ^ 2 + (2 * Real.pi / L) ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2) :=
    (Filter.eventually_ge_atTop K).mono fun J hJ =>
      torusFourierGreenCutoff_sub_cutoff_norm_le d L mass hL hmass f g K J hJ
  exact le_of_tendsto_of_tendsto ht tendsto_const_nhds hb

/-- A single cutoff controls the continuous tail. -/
theorem torusFourierGreenPairing_uniform_tail
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀,
      ‖torusFourierGreenPairing d L mass f g -
        torusFourierGreenCutoff d L mass f g K‖ < ε := by
  intro ε hε
  have ht := torusFourierGreenCutoff_error_norm_tendsto_zero d L mass hL hmass f g
  have hev : ∀ᶠ K : ℕ in Filter.atTop,
      ‖torusFourierGreenPairing d L mass f g -
        torusFourierGreenCutoff d L mass f g K‖ < ε :=
    ht.eventually (gt_mem_nhds hε)
  exact Filter.eventually_atTop.mp hev

end Pphi2Clean.Continuum
