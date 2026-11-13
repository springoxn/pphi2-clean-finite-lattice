import AImathPPhi2Clean.PeriodicFS4DCompactEmbedding
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

noncomputable section
namespace Pphi2Clean.Continuum

abbrev Periodic3DIndex := Fin 3 → ℤ

def periodic3DExtend (k : Periodic3DIndex) : FS4Index :=
  fun i => if h : i.val < 3 then k ⟨i.val, h⟩ else 0

theorem periodic3DExtend_injective : Function.Injective periodic3DExtend := by
  intro k l h
  funext i
  have hi : (⟨i.val, Nat.lt_trans i.isLt (by decide : 3 < 4)⟩ : Fin 4).val < 3 := by
    simpa using i.isLt
  have hval := congrFun h (⟨i.val, Nat.lt_trans i.isLt (by decide : 3 < 4)⟩ : Fin 4)
  simpa [periodic3DExtend, hi] using hval

def periodic3DSobolevWeight (s : ℝ) (k : Periodic3DIndex) : ℝ :=
  fs4SobolevWeight s (periodic3DExtend k)

def periodic3DHminusTwoWeight (k : Periodic3DIndex) : ℝ := periodic3DSobolevWeight 2 k
def periodic3DHminusThreeWeight (k : Periodic3DIndex) : ℝ := periodic3DSobolevWeight 3 k
def periodic3DHminusFourWeight (k : Periodic3DIndex) : ℝ := periodic3DSobolevWeight 4 k

theorem periodic3DSobolevWeight_nonneg (s : ℝ) (k : Periodic3DIndex) :
    0 ≤ periodic3DSobolevWeight s k := fs4SobolevWeight_nonneg s _

theorem periodic3DSobolevWeight_summable (s : ℝ) (hs : 2 < s) :
    Summable (periodic3DSobolevWeight s) := by
  exact (fs4SobolevWeight_summable s hs).comp_injective periodic3DExtend_injective

def periodic3DHminusTwoIndexSplit : Periodic3DIndex ≃ (Fin 2 → ℤ) × ℤ where
  toFun k := ((fun i : Fin 2 => k i.castSucc), k (Fin.last 2))
  invFun p := fun i => if h : i.val < 2 then p.1 ⟨i.val, h⟩ else p.2
  left_inv k := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    rcases p with ⟨q, n⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · simp

def periodic3DHminusTwoAxisWeight (n : ℤ) : ℝ :=
  if n = 0 then 1 else |(n : ℝ)| ^ (-(3 / 2 : ℝ))

theorem periodic3DHminusTwoAxisWeight_nonneg (n : ℤ) :
    0 ≤ periodic3DHminusTwoAxisWeight n := by
  by_cases hn : n = 0 <;> simp [periodic3DHminusTwoAxisWeight, hn, Real.rpow_nonneg]

theorem periodic3DHminusTwoAxisWeight_summable :
    Summable periodic3DHminusTwoAxisWeight := by
  have htail : Summable (fun n : ℤ =>
      if n = 0 then 0 else |(n : ℝ)| ^ (-(3 / 2 : ℝ))) := by
    have h := Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2)
    apply h.congr
    intro n
    by_cases hn : n = 0
    · simp [hn, Real.zero_rpow, ne_of_gt (by norm_num : (0 : ℝ) < 3 / 2)]
    · simp [hn]
  have hzero : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : ℤ)).subset
    intro n hn
    simp_all
  have hadd := hzero.add htail
  apply hadd.congr
  intro n
  by_cases hn : n = 0 <;> simp [periodic3DHminusTwoAxisWeight, hn]

def periodic3DHminusTwoProductWeight (p : (Fin 2 → ℤ) × ℤ) : ℝ :=
  fs4BlockWeight (5 / 2) p.1 * periodic3DHminusTwoAxisWeight p.2

theorem periodic3DHminusTwoProductWeight_nonneg (p : (Fin 2 → ℤ) × ℤ) :
    0 ≤ periodic3DHminusTwoProductWeight p :=
  mul_nonneg (fs4BlockWeight_nonneg _ _) (periodic3DHminusTwoAxisWeight_nonneg _)

theorem periodic3DHminusTwoProductWeight_summable :
    Summable periodic3DHminusTwoProductWeight := by
  apply (summable_prod_of_nonneg
    (fun p : (Fin 2 → ℤ) × ℤ => periodic3DHminusTwoProductWeight_nonneg p)).2
  constructor
  · intro q
    exact periodic3DHminusTwoAxisWeight_summable.mul_left (fs4BlockWeight (5 / 2) q)
  · have hblock : Summable (fs4BlockWeight (5 / 2)) :=
      fs4BlockWeight_summable (5 / 2) (by norm_num)
    have hconst : Summable (fun q : Fin 2 → ℤ =>
        fs4BlockWeight (5 / 2) q * (∑' n : ℤ, periodic3DHminusTwoAxisWeight n)) := hblock.mul_right _
    apply hconst.congr
    intro q
    simp only [periodic3DHminusTwoProductWeight]
    rw [tsum_mul_left]

lemma periodic3DHminusTwoMixedBound {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (1 + max x y) ^ (-4 : ℝ) ≤
      x ^ (-(5 / 2 : ℝ)) * y ^ (-(3 / 2 : ℝ)) := by
  let M := max x y
  have hMx : M ^ (-(5 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_left x y) (by norm_num)
  have hMy : M ^ (-(3 / 2 : ℝ)) ≤ y ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_right x y) (by norm_num)
  have hprod : M ^ (-4 : ℝ) ≤ x ^ (-(5 / 2 : ℝ)) * y ^ (-(3 / 2 : ℝ)) := by
    calc
      M ^ (-4 : ℝ) = M ^ (-(5 / 2 : ℝ)) * M ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add (by positivity)]
        norm_num
      _ ≤ x ^ (-(5 / 2 : ℝ)) * y ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul hMx hMy (by positivity) (by positivity)
  have hbase : M ≤ 1 + M := by
    dsimp [M]
    linarith [le_max_left x y]
  exact (Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)).trans hprod

lemma periodic3DHminusTwoSplitCoordinates (k : Periodic3DIndex) :
    (fs4SplitIndex (periodic3DExtend k)).1 = (periodic3DHminusTwoIndexSplit k).1 ∧
    (fs4SplitIndex (periodic3DExtend k)).2 = ![(periodic3DHminusTwoIndexSplit k).2, 0] := by
  constructor
  · ext i
    fin_cases i <;>
      simp [periodic3DHminusTwoIndexSplit, fs4SplitIndex, periodic3DExtend, finSumFinEquiv]
  · ext i
    fin_cases i <;>
      simp [periodic3DHminusTwoIndexSplit, fs4SplitIndex, periodic3DExtend, finSumFinEquiv]

lemma periodic3DSobolevWeight_two_le_product (k : Periodic3DIndex) :
    periodic3DSobolevWeight 2 k ≤
      periodic3DHminusTwoProductWeight (periodic3DHminusTwoIndexSplit k) := by
  let q := (periodic3DHminusTwoIndexSplit k).1
  let n := (periodic3DHminusTwoIndexSplit k).2
  have hcoords := periodic3DHminusTwoSplitCoordinates k
  have hnrm : ‖![n, 0]‖ = |(n : ℝ)| := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp
  have hweight : periodic3DSobolevWeight 2 k =
      (1 + max ‖q‖ |(n : ℝ)|) ^ (-4 : ℝ) := by
    unfold periodic3DSobolevWeight fs4SobolevWeight
    rw [hcoords.1, hcoords.2, hnrm]
    norm_num [q]
  rw [hweight]
  change (1 + max ‖q‖ |(n : ℝ)|) ^ (-4 : ℝ) ≤
    fs4BlockWeight (5 / 2) q * periodic3DHminusTwoAxisWeight n
  by_cases hq : q = 0
  · by_cases hn : n = 0
    · simp [fs4BlockWeight, periodic3DHminusTwoAxisWeight, hq, hn]
    · have hy : 1 ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hn
      have h1 : (1 + |(n : ℝ)|) ^ (-4 : ℝ) ≤ |(n : ℝ)| ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have h2 : |(n : ℝ)| ^ (-4 : ℝ) ≤ |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
      simpa [fs4BlockWeight, periodic3DHminusTwoAxisWeight, hq, hn] using h1.trans h2
  · have hx : 1 ≤ ‖q‖ := one_le_norm_int_frequency q hq
    by_cases hn : n = 0
    · have h1 : (1 + ‖q‖) ^ (-4 : ℝ) ≤ ‖q‖ ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have h2 : ‖q‖ ^ (-4 : ℝ) ≤ ‖q‖ ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      simpa [fs4BlockWeight, periodic3DHminusTwoAxisWeight, hq, hn] using h1.trans h2
    · have hy : 1 ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hn
      have hmain := periodic3DHminusTwoMixedBound hx hy
      simpa [fs4BlockWeight, periodic3DHminusTwoAxisWeight, hq, hn] using hmain

theorem periodic3DHminusTwoWeight_summable :
    Summable periodic3DHminusTwoWeight := by
  have hmajor : Summable (fun k : Periodic3DIndex =>
      periodic3DHminusTwoProductWeight (periodic3DHminusTwoIndexSplit k)) :=
    periodic3DHminusTwoProductWeight_summable.comp_injective
      periodic3DHminusTwoIndexSplit.injective
  exact Summable.of_nonneg_of_le
    (fun k => periodic3DSobolevWeight_nonneg 2 k)
    periodic3DSobolevWeight_two_le_product
    hmajor

theorem periodic3DHminusThreeWeight_summable :
    Summable periodic3DHminusThreeWeight := periodic3DSobolevWeight_summable 3 (by norm_num)

theorem periodic3DHminusFourWeight_summable :
    Summable periodic3DHminusFourWeight := periodic3DSobolevWeight_summable 4 (by norm_num)

theorem periodic3DHminusFourWeight_le_three (k : Periodic3DIndex) :
    periodic3DHminusFourWeight k ≤ periodic3DHminusThreeWeight k :=
  fs4_weight_four_le_three (periodic3DExtend k)

end Pphi2Clean.Continuum
