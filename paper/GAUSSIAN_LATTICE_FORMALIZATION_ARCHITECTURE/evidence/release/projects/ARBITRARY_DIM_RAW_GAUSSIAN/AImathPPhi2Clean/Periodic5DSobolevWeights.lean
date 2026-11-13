import AImathPPhi2Clean.PeriodicFS4DSobolevWeights
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
namespace Pphi2Clean.Continuum

abbrev Periodic5DIndex := Fin 5 → ℤ

def periodic5DSobolevWeight (s : ℝ) (k : Periodic5DIndex) : ℝ :=
  (1 + ‖k‖) ^ (-2 * s)

abbrev periodic5DHminusThreeWeight := periodic5DSobolevWeight 3

theorem periodic5DSobolevWeight_nonneg (s : ℝ) (k : Periodic5DIndex) :
    0 ≤ periodic5DSobolevWeight s k := Real.rpow_nonneg (by positivity) _

theorem periodic5DSobolevWeight_pos (s : ℝ) (k : Periodic5DIndex) :
    0 < periodic5DSobolevWeight s k := Real.rpow_pos_of_pos (by positivity) _

private def block (q : Fin 2 → ℤ) : ℝ := (1 + ‖q‖) ^ (-(17 / 8 : ℝ))
private def axis (n : ℤ) : ℝ := if n = 0 then 1 else |(n : ℝ)| ^ (-(5 / 4 : ℝ))

private theorem block_summable : Summable block := by
  apply Summable.of_nonneg_of_le (fun q => Real.rpow_nonneg (by positivity) _)
    (f := fs4BlockWeight (17 / 8))
  · intro q
    by_cases hq : q = 0
    · simp [block, fs4BlockWeight, hq]
    · simpa [block, fs4BlockWeight, hq] using
        Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hq)
          (show ‖q‖ ≤ 1 + ‖q‖ by linarith) (by norm_num : -(17 / 8 : ℝ) ≤ 0)
  · exact fs4BlockWeight_summable _ (by norm_num)

private theorem axis_nonneg (n : ℤ) : 0 ≤ axis n := by
  by_cases hn : n = 0 <;> simp [axis, hn, Real.rpow_nonneg]

private theorem axis_summable : Summable axis := by
  have h := Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 5 / 4)
  have hz : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : ℤ)).subset
    intro n hn
    simp_all
  apply (hz.add h).congr
  intro n
  by_cases hn : n = 0
  · simp [axis, hn, Real.zero_rpow, show -(5 / 4 : ℝ) ≠ 0 by norm_num]
  · simp [axis, hn]

private def split : Periodic5DIndex ≃ ((Fin 2 → ℤ) × (Fin 2 → ℤ)) × ℤ where
  toFun k := (((fun i => k ⟨i.val, by omega⟩),
    (fun i => k ⟨i.val + 2, by omega⟩)), k 4)
  invFun p := fun i => if h : i.val < 2 then p.1.1 ⟨i.val,h⟩
    else if h' : i.val < 4 then p.1.2 ⟨i.val - 2, by omega⟩ else p.2
  left_inv k := by funext i; fin_cases i <;> simp
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext <;> funext i <;> fin_cases i <;> simp
    · simp

private def major (p : ((Fin 2 → ℤ) × (Fin 2 → ℤ)) × ℤ) : ℝ :=
  (block p.1.1 * block p.1.2) * axis p.2

private theorem major_summable : Summable major := by
  exact (block_summable.mul_of_nonneg block_summable
    (fun q => Real.rpow_nonneg (by positivity) _) (fun q => Real.rpow_nonneg (by positivity) _)).mul_of_nonneg
    axis_summable (fun q => mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)) axis_nonneg

private theorem weight_le_major (k : Periodic5DIndex) :
    periodic5DSobolevWeight (11 / 4) k ≤ major (split k) := by
  let M := 1 + ‖k‖
  have hM : 0 < M := by dsimp [M]; positivity
  have hq1 : ‖(split k).1.1‖ ≤ ‖k‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg k)).2
    intro i
    exact norm_le_pi_norm k _
  have hq2 : ‖(split k).1.2‖ ≤ ‖k‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg k)).2
    intro i
    exact norm_le_pi_norm k _
  have h1 : M ^ (-(17 / 8 : ℝ)) ≤ block (split k).1.1 :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [M]; linarith) (by norm_num)
  have h2 : M ^ (-(17 / 8 : ℝ)) ≤ block (split k).1.2 :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [M]; linarith) (by norm_num)
  have h3 : M ^ (-(5 / 4 : ℝ)) ≤ axis (split k).2 := by
    by_cases hn : (split k).2 = 0
    · simp only [axis, hn, if_pos]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by dsimp [M]; linarith [norm_nonneg k]) (by norm_num)
    · have hab : |((split k).2 : ℝ)| ≤ ‖k‖ := by
        simpa [split, Int.norm_eq_abs, Int.cast_abs] using norm_le_pi_norm k (4 : Fin 5)
      have ha : 0 < |((split k).2 : ℝ)| := by positivity
      simpa [axis, hn] using Real.rpow_le_rpow_of_nonpos ha
        (show |((split k).2 : ℝ)| ≤ M by dsimp [M]; linarith) (by norm_num : -(5 / 4 : ℝ) ≤ 0)
  have h12 := mul_le_mul h1 h2 (Real.rpow_nonneg hM.le _) (by dsimp [block]; positivity)
  have hall := mul_le_mul h12 h3 (Real.rpow_nonneg hM.le _) (mul_nonneg (by dsimp [block]; positivity) (by dsimp [block]; positivity))
  have heq : (M ^ (-(17 / 8 : ℝ)) * M ^ (-(17 / 8 : ℝ))) * M ^ (-(5 / 4 : ℝ)) = M ^ (-(11 / 2) : ℝ) := by
    rw [← Real.rpow_add hM, ← Real.rpow_add hM]
    norm_num
  rw [heq] at hall
  change (1 + ‖k‖) ^ (-2 * (11 / 4 : ℝ)) ≤ _
  norm_num only [show -2 * (11 / 4 : ℝ) = -(11 / 2) by norm_num]
  exact hall

theorem periodic5DSobolevWeight_eleven_quarters_summable :
    Summable (periodic5DSobolevWeight (11 / 4)) := by
  exact Summable.of_nonneg_of_le (periodic5DSobolevWeight_nonneg _)
    weight_le_major (major_summable.comp_injective split.injective)

theorem periodic5DSobolevWeight_antitone {s t : ℝ} (hst : s ≤ t)
    (k : Periodic5DIndex) : periodic5DSobolevWeight t k ≤ periodic5DSobolevWeight s k := by
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg k]) (by linarith)

theorem periodic5DHminusThreeWeight_summable : Summable periodic5DHminusThreeWeight := by
  exact Summable.of_nonneg_of_le (periodic5DSobolevWeight_nonneg 3)
    (periodic5DSobolevWeight_antitone (by norm_num : (11 / 4 : ℝ) ≤ 3))
    periodic5DSobolevWeight_eleven_quarters_summable

def periodic5DHminusThreeWeightTail (K : Finset Periodic5DIndex) : ℝ :=
  ∑' k : {k : Periodic5DIndex // k ∉ K}, periodic5DHminusThreeWeight k

theorem periodic5DHminusThreeWeightTail_nonneg (K : Finset Periodic5DIndex) :
    0 ≤ periodic5DHminusThreeWeightTail K :=
  tsum_nonneg fun k => periodic5DSobolevWeight_nonneg 3 k

theorem periodic5DHminusThreeWeightTail_tendsto_zero :
    Filter.Tendsto periodic5DHminusThreeWeightTail Filter.atTop (nhds 0) :=
  tendsto_tsum_compl_atTop_zero periodic5DHminusThreeWeight

theorem periodic5DHminusThreeWeightTail_exists_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Finset Periodic5DIndex, periodic5DHminusThreeWeightTail K < ε := by
  exact ((tendsto_order.1 periodic5DHminusThreeWeightTail_tendsto_zero).2 ε hε).exists

end Pphi2Clean.Continuum
