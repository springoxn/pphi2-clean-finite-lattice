import AImathPPhi2Clean.PeriodicNegativeSobolevWeightComparison
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

noncomputable section
namespace Pphi2Clean.Continuum

abbrev FS4Index := Fin 4 → ℤ
abbrev FS4PairIndex := (Fin 2 → ℤ) × (Fin 2 → ℤ)

def fs4SplitIndex : FS4Index ≃ FS4PairIndex :=
  ((finSumFinEquiv (m := 2) (n := 2)).symm.arrowCongr (Equiv.refl ℤ)).trans
    (Equiv.sumArrowEquivProdArrow (Fin 2) (Fin 2) ℤ)

def fs4BlockWeight (s : ℝ) (k : Fin 2 → ℤ) : ℝ :=
  if k = 0 then 1 else ‖k‖ ^ (-s)

theorem fs4BlockWeight_nonneg (s : ℝ) (k : Fin 2 → ℤ) : 0 ≤ fs4BlockWeight s k := by
  by_cases hk : k = 0
  · simp [fs4BlockWeight, hk]
  · simp [fs4BlockWeight, hk, Real.rpow_nonneg]

theorem fs4BlockWeight_summable (s : ℝ) (hs : 2 < s) : Summable (fs4BlockWeight s) := by
  have hzero : Summable (fun k : Fin 2 → ℤ => if k = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : Fin 2 → ℤ)).subset
    intro k hk
    simp_all
  have htail : Summable (fun k : Fin 2 → ℤ => if k = 0 then 0 else ‖k‖ ^ (-s)) := by
    have h := EisensteinSeries.summable_one_div_norm_rpow hs
    apply h.congr
    intro k
    by_cases hk : k = 0
    · simp [hk, Real.zero_rpow, ne_of_gt (by linarith : 0 < s)]
    · simp [hk]
  have hadd := hzero.add htail
  apply hadd.congr
  intro k
  by_cases hk : k = 0 <;> simp [fs4BlockWeight, hk]

def fs4SobolevWeight (s : ℝ) (k : FS4Index) : ℝ :=
  (1 + max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖) ^ (-2 * s)

theorem fs4SobolevWeight_nonneg (s : ℝ) (k : FS4Index) : 0 ≤ fs4SobolevWeight s k := by
  exact Real.rpow_nonneg (by positivity) _

lemma fs4_max_radial_product_bound (s : ℝ) (hs : 2 < s)
    (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (1 + max x y) ^ (-2 * s) ≤ x ^ (-s) * y ^ (-s) := by
  let M := max x y
  have hM : 1 ≤ M := le_trans hx (le_max_left x y)
  have hneg : -s ≤ 0 := by linarith
  have hMx : M ^ (-s) ≤ x ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_left x y) hneg
  have hMy : M ^ (-s) ≤ y ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_right x y) hneg
  have hsq : M ^ (-2 * s) ≤ x ^ (-s) * y ^ (-s) := by
    calc
      M ^ (-2 * s) = M ^ (-s) * M ^ (-s) := by
        rw [← Real.rpow_add (by positivity)]
        ring
      _ ≤ x ^ (-s) * y ^ (-s) :=
        mul_le_mul hMx hMy (by positivity) (by positivity)
  have hbase : M ≤ 1 + M := by linarith
  have hfinal : (1 + M) ^ (-2 * s) ≤ M ^ (-2 * s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  simpa [M] using le_trans hfinal hsq

lemma fs4_oneplus_pow_le_pow (s : ℝ) (hs : 2 < s) (x : ℝ) (hx : 1 ≤ x) :
    (1 + x) ^ (-2 * s) ≤ x ^ (-s) := by
  have h1 : (1 + x) ^ (-2 * s) ≤ x ^ (-2 * s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h2 : x ^ (-2 * s) ≤ x ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  exact le_trans h1 h2

theorem fs4SobolevWeight_le_pairMajorant (s : ℝ) (hs : 2 < s) (k : FS4Index) :
    fs4SobolevWeight s k ≤
      fs4BlockWeight s (fs4SplitIndex k).1 * fs4BlockWeight s (fs4SplitIndex k).2 := by
  let q1 := (fs4SplitIndex k).1
  let q2 := (fs4SplitIndex k).2
  by_cases hq1 : q1 = 0
  · by_cases hq2 : q2 = 0
    · simp [fs4SobolevWeight, fs4BlockWeight, q1, q2, hq1, hq2]
    · have hy : 1 ≤ ‖q2‖ := one_le_norm_int_frequency q2 hq2
      have hbound := fs4_oneplus_pow_le_pow s hs ‖q2‖ hy
      simpa [fs4SobolevWeight, fs4BlockWeight, q1, q2, hq1, hq2] using hbound
  · by_cases hq2 : q2 = 0
    · have hx : 1 ≤ ‖q1‖ := one_le_norm_int_frequency q1 hq1
      have hbound := fs4_oneplus_pow_le_pow s hs ‖q1‖ hx
      simpa [fs4SobolevWeight, fs4BlockWeight, q1, q2, hq1, hq2, max_comm] using hbound
    · have hx : 1 ≤ ‖q1‖ := one_le_norm_int_frequency q1 hq1
      have hy : 1 ≤ ‖q2‖ := one_le_norm_int_frequency q2 hq2
      have hbound := fs4_max_radial_product_bound s hs ‖q1‖ ‖q2‖ hx hy
      simpa [fs4SobolevWeight, fs4BlockWeight, q1, q2, hq1, hq2] using hbound

theorem fs4SobolevWeight_summable (s : ℝ) (hs : 2 < s) : Summable (fs4SobolevWeight s) := by
  have hpair : Summable (fun p : FS4PairIndex => fs4BlockWeight s p.1 * fs4BlockWeight s p.2) :=
    (fs4BlockWeight_summable s hs).mul_of_nonneg (fs4BlockWeight_summable s hs)
      (fs4BlockWeight_nonneg s) (fs4BlockWeight_nonneg s)
  have hmajor : Summable (fun k : FS4Index =>
      fs4BlockWeight s (fs4SplitIndex k).1 * fs4BlockWeight s (fs4SplitIndex k).2) :=
    (fs4SplitIndex.summable_iff
      (f := fun p : FS4PairIndex => fs4BlockWeight s p.1 * fs4BlockWeight s p.2)).2 hpair
  exact Summable.of_nonneg_of_le (fs4SobolevWeight_nonneg s)
    (fs4SobolevWeight_le_pairMajorant s hs) hmajor

theorem fs4HMinusThreeWeight_summable :
    Summable (fs4SobolevWeight 3) := fs4SobolevWeight_summable 3 (by norm_num)

theorem fs4HMinusFourWeight_summable :
    Summable (fs4SobolevWeight 4) := fs4SobolevWeight_summable 4 (by norm_num)

def fs4BlockBox (T : ℝ) : Set (Fin 2 → ℤ) :=
  Set.univ.pi (fun _ : Fin 2 => Set.Icc (-(⌈T⌉₊ : ℤ)) (⌈T⌉₊ : ℤ))

theorem fs4_weight_ratio_tendsto_zero :
    ∀ δ : ℝ, 0 < δ → ∃ K : Finset FS4Index,
      ∀ k, k ∉ K → fs4SobolevWeight 4 k ≤ δ * fs4SobolevWeight 3 k := by
  intro δ hδ
  let T : ℝ := max 1 (δ⁻¹ + 1)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTδ : δ⁻¹ < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  let box := fs4BlockBox T
  have hbox : box.Finite := by
    change (Set.univ.pi (fun _ : Fin 2 =>
      Set.Icc (-(⌈T⌉₊ : ℤ)) (⌈T⌉₊ : ℤ))).Finite
    apply Set.Finite.pi
    intro i
    exact Set.finite_Icc _ _
  let Kset : Set FS4Index := fs4SplitIndex ⁻¹' (box ×ˢ box)
  have hKset : Kset.Finite := by
    dsimp [Kset]
    exact (hbox.prod hbox).preimage
      (Set.injOn_of_injective fs4SplitIndex.injective)
  let K := hKset.toFinset
  refine ⟨K, ?_⟩
  intro k hk
  have hkFin : k ∉ hKset.toFinset := by simpa [K] using hk
  have hKnot : k ∉ Kset := (hKset.mem_toFinset).not.mp hkFin
  have hsplitnot : ¬ ((fs4SplitIndex k).1 ∈ box ∧ (fs4SplitIndex k).2 ∈ box) := by
    simpa [Kset, Set.mem_preimage, Set.mem_prod] using hKnot
  have hnorm_of_not_box (q : Fin 2 → ℤ) (hq : q ∉ box) : T < ‖q‖ := by
    have hq' : ¬ ∀ i, q i ∈ Set.Icc (-(⌈T⌉₊ : ℤ)) (⌈T⌉₊ : ℤ) := by
      intro hcoords
      apply hq
      change q ∈ Set.univ.pi _
      rw [Set.mem_univ_pi]
      exact hcoords
    by_contra hnot
    have hle : ‖q‖ ≤ T := le_of_not_gt hnot
    rw [EisensteinSeries.norm_eq_max_natAbs] at hle
    have hmax : max (q 0).natAbs (q 1).natAbs ≤ ⌈T⌉₊ := by
      exact_mod_cast le_trans hle (Nat.le_ceil T)
    have hcoord : ∀ i, q i ∈ Set.Icc (-(⌈T⌉₊ : ℤ)) (⌈T⌉₊ : ℤ) := by
      intro i
      have hnat : (q i).natAbs ≤ ⌈T⌉₊ := by
        fin_cases i
        · exact (max_le_iff.mp hmax).1
        · exact (max_le_iff.mp hmax).2
      have habs : |q i| ≤ (⌈T⌉₊ : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hnat
      exact abs_le.mp habs
    exact hq' hcoord
  have hsmall (hM : T < max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖) :
      (1 + max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖) ^ (-2 : ℝ) ≤ δ := by
    let M := max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖
    have hMd : δ⁻¹ < M := lt_trans hTδ hM
    have hmul : 1 < M * δ := (inv_lt_iff_one_lt_mul₀ hδ).mp hMd
    have hMpos : 0 < M := lt_trans (by linarith : 0 < T) hM
    have hinv : M⁻¹ ≤ δ := by
      rw [inv_le_iff_one_le_mul₀ hMpos]
      exact (by simpa [mul_comm] using hmul.le)
    have hMone : 1 ≤ M := le_trans hT1 (le_of_lt hM)
    have hpow : M ^ (-2 : ℝ) ≤ M ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hMone (by norm_num)
    have hcalc : (1 + M) ^ (-2 : ℝ) ≤ δ := by
      calc
        (1 + M) ^ (-2 : ℝ) ≤ M ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
        _ ≤ M ^ (-1 : ℝ) := hpow
        _ = M⁻¹ := Real.rpow_neg_one M
        _ ≤ δ := hinv
    simpa [M] using hcalc
  have hpower : fs4SobolevWeight 4 k = fs4SobolevWeight 3 k *
      (1 + max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖) ^ (-2 : ℝ) := by
    dsimp [fs4SobolevWeight]
    rw [← Real.rpow_add (by positivity)]
    norm_num
  rcases not_and_or.mp hsplitnot with hq1 | hq2
  · have hM : T < max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖ :=
      lt_of_lt_of_le (hnorm_of_not_box _ hq1) (le_max_left _ _)
    rw [hpower]
    calc
      fs4SobolevWeight 3 k *
          (1 + max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖) ^ (-2 : ℝ) ≤
        fs4SobolevWeight 3 k * δ :=
          mul_le_mul_of_nonneg_left (hsmall hM) (fs4SobolevWeight_nonneg 3 k)
      _ = δ * fs4SobolevWeight 3 k := by ring
  · have hM : T < max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖ :=
      lt_of_lt_of_le (hnorm_of_not_box _ hq2) (le_max_right _ _)
    rw [hpower]
    calc
      fs4SobolevWeight 3 k *
          (1 + max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖) ^ (-2 : ℝ) ≤
        fs4SobolevWeight 3 k * δ :=
          mul_le_mul_of_nonneg_left (hsmall hM) (fs4SobolevWeight_nonneg 3 k)
      _ = δ * fs4SobolevWeight 3 k := by ring

theorem fs4_hminus4_tail_sq_le_of_weight_ratio
    {c : FS4Index → ℂ} (K : Finset FS4Index) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hweight : ∀ k, k ∉ K → fs4SobolevWeight 4 k ≤ δ * fs4SobolevWeight 3 k)
    (hc : Summable (fun k : FS4Index => fs4SobolevWeight 3 k * ‖c k‖ ^ 2)) :
    (∑' k, if k ∉ K then fs4SobolevWeight 4 k * ‖c k‖ ^ 2 else 0) ≤
      δ * (∑' k, fs4SobolevWeight 3 k * ‖c k‖ ^ 2) := by
  have hmajor : Summable (fun k : FS4Index =>
      δ * (fs4SobolevWeight 3 k * ‖c k‖ ^ 2)) := by
    simpa only [mul_assoc] using hc.mul_left δ
  have htail : Summable (fun k : FS4Index => if k ∉ K then
      fs4SobolevWeight 4 k * ‖c k‖ ^ 2 else 0) := by
    refine Summable.of_nonneg_of_le
      (f := fun k : FS4Index => δ * (fs4SobolevWeight 3 k * ‖c k‖ ^ 2))
      (g := fun k : FS4Index => if k ∉ K then
        fs4SobolevWeight 4 k * ‖c k‖ ^ 2 else 0) ?_ ?_ hmajor
    · intro k
      by_cases hk : k ∈ K
      · simp [hk]
      · simp [hk]
        exact mul_nonneg (fs4SobolevWeight_nonneg 4 k) (sq_nonneg _)
    · intro k
      by_cases hk : k ∈ K
      · simp [hk]
        exact mul_nonneg hδ (mul_nonneg (fs4SobolevWeight_nonneg 3 k) (sq_nonneg _))
      · simp [hk]
        simpa [hk, mul_assoc] using
          (mul_le_mul_of_nonneg_right (hweight k hk) (sq_nonneg (‖c k‖)))
  calc
    (∑' k : FS4Index, if k ∉ K then
        fs4SobolevWeight 4 k * ‖c k‖ ^ 2 else 0) ≤
        ∑' k, δ * (fs4SobolevWeight 3 k * ‖c k‖ ^ 2) := by
      exact htail.tsum_le_tsum (fun k => by
        by_cases hk : k ∈ K
        · simp [hk]
          exact mul_nonneg hδ (mul_nonneg (fs4SobolevWeight_nonneg 3 k) (sq_nonneg _))
        · simp [hk]
          simpa [hk, mul_assoc] using
            (mul_le_mul_of_nonneg_right (hweight k hk) (sq_nonneg (‖c k‖)))) hmajor
    _ = δ * (∑' k, fs4SobolevWeight 3 k * ‖c k‖ ^ 2) := by
      rw [tsum_mul_left]

def fs4HminusThreeNorm (c : FS4Index → ℂ) : ℝ :=
  Real.sqrt (∑' k, fs4SobolevWeight 3 k * ‖c k‖ ^ 2)

theorem fs4_hminus4_uniform_tail_of_hminus3_bound :
    ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
      ∃ K : Finset FS4Index, ∀ c : FS4Index → ℂ,
        Summable (fun k => fs4SobolevWeight 3 k * ‖c k‖ ^ 2) →
        fs4HminusThreeNorm c ≤ R →
        Real.sqrt (∑' k, if k ∉ K then
          fs4SobolevWeight 4 k * ‖c k‖ ^ 2 else 0) < ε := by
  intro R hR ε hε
  let δ := (ε / (R + 1)) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨K, hK⟩ := fs4_weight_ratio_tendsto_zero δ hδ
  refine ⟨K, ?_⟩
  intro c hc hnorm
  have hnorm_sq :
      (∑' k : FS4Index, fs4SobolevWeight 3 k * ‖c k‖ ^ 2) ≤ R ^ 2 := by
    change Real.sqrt (∑' k : FS4Index,
      fs4SobolevWeight 3 k * ‖c k‖ ^ 2) ≤ R at hnorm
    exact (Real.sqrt_le_iff).mp hnorm |>.2
  have htail := fs4_hminus4_tail_sq_le_of_weight_ratio K δ hδ.le hK hc
  have htail_nonneg : 0 ≤ ∑' k : FS4Index, if k ∉ K then
      fs4SobolevWeight 4 k * ‖c k‖ ^ 2 else 0 :=
    tsum_nonneg fun k => by
      by_cases hk : k ∉ K
      · simp [hk]
        exact mul_nonneg (fs4SobolevWeight_nonneg 4 k) (sq_nonneg ‖c k‖)
      · simp [hk]
  apply (Real.sqrt_lt htail_nonneg hε.le).2
  calc
    (∑' k : FS4Index, if k ∉ K then
        fs4SobolevWeight 4 k * ‖c k‖ ^ 2 else 0) ≤
        δ * (∑' k : FS4Index,
          fs4SobolevWeight 3 k * ‖c k‖ ^ 2) := htail
    _ ≤ δ * R ^ 2 := mul_le_mul_of_nonneg_left hnorm_sq hδ.le
    _ < ε ^ 2 := by
      dsimp [δ]
      have hden : 0 < R + 1 := by linarith
      have hratio_nonneg : 0 ≤ R / (R + 1) := div_nonneg hR hden.le
      have hratio_lt : R / (R + 1) < 1 := (div_lt_one hden).2 (by linarith)
      have hratio_sq : (R / (R + 1)) ^ 2 < 1 := by
        have hsum_pos : 0 < 1 + R / (R + 1) := by linarith
        nlinarith [mul_pos (sub_pos.mpr hratio_lt) hsum_pos]
      have hcalc :
          (ε / (R + 1)) ^ 2 * R ^ 2 =
            ε ^ 2 * (R / (R + 1)) ^ 2 := by
        field_simp [ne_of_gt hden] <;> ring
      rw [hcalc]
      calc
        ε ^ 2 * (R / (R + 1)) ^ 2 < ε ^ 2 * 1 :=
          mul_lt_mul_of_pos_left hratio_sq (sq_pos_of_pos hε)
        _ = ε ^ 2 := by ring

end Pphi2Clean.Continuum
namespace Pphi2Clean.Continuum

lemma fs4_max_four_abs_sq_le_sum {a b c d S : ℝ} (hS : 0 ≤ S)
    (ha : a ^ 2 ≤ S) (hb : b ^ 2 ≤ S) (hc : c ^ 2 ≤ S) (hd : d ^ 2 ≤ S) :
    max (max |a| |b|) (max |c| |d|) ^ 2 ≤ S := by
  have hroot (x : ℝ) (hx : x ^ 2 ≤ S) : |x| ≤ Real.sqrt S := by
    apply (Real.le_sqrt (abs_nonneg x) hS).2
    simpa [sq_abs] using hx
  have hab : max |a| |b| ≤ Real.sqrt S :=
    (max_le_iff).2 ⟨hroot a ha, hroot b hb⟩
  have hcd : max |c| |d| ≤ Real.sqrt S :=
    (max_le_iff).2 ⟨hroot c hc, hroot d hd⟩
  have hm : max (max |a| |b|) (max |c| |d|) ≤ Real.sqrt S :=
    (max_le_iff).2 ⟨hab, hcd⟩
  have hmn : 0 ≤ max (max |a| |b|) (max |c| |d|) := by positivity
  have hsqrt : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS
  have hsq : max (max |a| |b|) (max |c| |d|) ^ 2 ≤ (Real.sqrt S) ^ 2 :=
    (sq_le_sq₀ hmn (Real.sqrt_nonneg S)).2 hm
  simpa [hsqrt] using hsq

lemma fs4_split_norm_sq_le_energy (k : FS4Index) :
    max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖ ^ 2 ≤
      ∑ i : Fin 4, (k i : ℝ)^2 := by
  let e := finSumFinEquiv (m := 2) (n := 2)
  have he0 : e (Sum.inl (0 : Fin 2)) = 0 := by decide
  have he1 : e (Sum.inl (1 : Fin 2)) = 1 := by decide
  have he2 : e (Sum.inr (0 : Fin 2)) = 2 := by decide
  have he3 : e (Sum.inr (1 : Fin 2)) = 3 := by decide
  have hS : 0 ≤ ∑ i : Fin 4, (k i : ℝ)^2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hcoord (j : Fin 4) : (k j : ℝ)^2 ≤ ∑ i : Fin 4, (k i : ℝ)^2 :=
    Finset.single_le_sum (fun i hi => sq_nonneg (k i : ℝ)) (Finset.mem_univ j)
  have hmain := fs4_max_four_abs_sq_le_sum hS
    (hcoord 0) (hcoord 1) (hcoord 2) (hcoord 3)
  rw [EisensteinSeries.norm_eq_max_natAbs, EisensteinSeries.norm_eq_max_natAbs]
  simpa [fs4SplitIndex, e, he0, he1, he2, he3, Int.natCast_natAbs] using hmain

end Pphi2Clean.Continuum
