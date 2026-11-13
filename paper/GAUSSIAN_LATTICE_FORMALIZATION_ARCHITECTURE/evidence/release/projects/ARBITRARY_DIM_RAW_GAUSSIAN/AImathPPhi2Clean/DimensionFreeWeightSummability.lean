import AImathPPhi2Clean.Periodic5DSobolevWeights
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
noncomputable section
namespace Pphi2Clean.DimensionFreeProbe

def axisWeight (q : ℝ) (z : ℤ) : ℝ := if z = 0 then 1 else ‖z‖ ^ (-q)
def regularizedAxisWeight (q : ℝ) (z : ℤ) : ℝ := (1 + ‖(z : ℝ)‖) ^ (-q)

lemma axisWeight_nonneg (q : ℝ) (z : ℤ) : 0 ≤ axisWeight q z := by
  by_cases hz : z = 0
  · simp [axisWeight, hz]
  · simp [axisWeight, hz, Real.rpow_nonneg]
lemma regularizedAxisWeight_nonneg (q : ℝ) (z : ℤ) : 0 ≤ regularizedAxisWeight q z :=
  Real.rpow_nonneg (by positivity) _
lemma regularizedAxisWeight_le_axisWeight (q : ℝ) (hq : 0 ≤ q) (z : ℤ) :
    regularizedAxisWeight q z ≤ axisWeight q z := by
  by_cases hz : z = 0
  · simp [regularizedAxisWeight, axisWeight, hz]
  · have hzInt : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
    have hzReal : (1 : ℝ) ≤ ‖(z : ℝ)‖ := by
      rw [Real.norm_eq_abs, ← Int.cast_abs]
      exact_mod_cast hzInt
    have hnorm : ‖(z : ℝ)‖ = ‖z‖ := by simp [Real.norm_eq_abs, Int.norm_eq_abs]
    rw [regularizedAxisWeight, axisWeight, if_neg hz, ← hnorm]
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · linarith
    · exact neg_nonpos.mpr hq

lemma axisWeight_summable (q : ℝ) (hq : 1 < q) : Summable (axisWeight q) := by
  have hzero : Summable (fun z : ℤ => if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : ℤ)).subset
    intro z hz
    simp_all
  have htail : Summable (fun z : ℤ => if z = 0 then 0 else ‖z‖ ^ (-q)) := by
    have h := Real.summable_abs_int_rpow hq
    apply h.congr
    intro z
    by_cases hz : z = 0
    · simp [hz, Real.zero_rpow, ne_of_gt (by linarith : 0 < q)]
    · simp [hz, Int.norm_eq_abs]
  have hadd := hzero.add htail
  apply hadd.congr
  intro z
  by_cases hz : z = 0 <;> simp [axisWeight, hz]

lemma summable_tensor {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  rw [summable_prod_of_nonneg (fun p => mul_nonneg (hf0 p.1) (hg0 p.2))]
  constructor
  · intro x
    exact hg.mul_left (f x)
  · have houter : Summable (fun x : α => f x * ∑' y : β, g y) := hf.mul_right _
    simpa only [tsum_mul_left] using houter

def splitIndex (n : ℕ) : (Fin (n + 1) → ℤ) ≃ (ℤ × (Fin n → ℤ)) where
  toFun k := (k 0, fun i => k i.succ)
  invFun p := Fin.cases p.1 (fun i => p.2 i)
  left_inv k := by
    funext i
    exact Fin.cases (by rfl) (fun j => by rfl) i
  right_inv p := by
    rcases p with ⟨z, k⟩
    simp

def productWeight (q : ℝ) : (d : ℕ) → (Fin d → ℤ) → ℝ
  | 0, _ => 1
  | n + 1, k => axisWeight q (k 0) * productWeight q n (fun i => k i.succ)
lemma productWeight_eq_prod (q : ℝ) (d : ℕ) (k : Fin d → ℤ) :
    productWeight q d k = ∏ i : Fin d, axisWeight q (k i) := by
  induction d with
  | zero => simp [productWeight]
  | succ n ih => simp only [productWeight, Fin.prod_univ_succ, ih]
lemma productWeight_nonneg (q : ℝ) (d : ℕ) (k : Fin d → ℤ) :
    0 ≤ productWeight q d k := by
  induction d with
  | zero => simp [productWeight]
  | succ n ih =>
      simp only [productWeight]
      exact mul_nonneg (axisWeight_nonneg q (k 0)) (ih (fun i => k i.succ))
lemma productWeight_summable (q : ℝ) (hq : 1 < q) (d : ℕ) :
    Summable (productWeight q d) := by
  induction d with
  | zero =>
      simpa [productWeight] using
        (Summable.of_finite : Summable (fun _ : Fin 0 → ℤ => (1 : ℝ)))
  | succ n ih =>
      let e := splitIndex n
      let pairW : (ℤ × (Fin n → ℤ)) → ℝ :=
        fun p => axisWeight q p.1 * productWeight q n p.2
      have heq : productWeight q (n + 1) = pairW ∘ e := by
        funext k
        rfl
      rw [heq]
      apply (e.summable_iff).mpr
      exact summable_tensor (axisWeight_summable q hq) ih
        (axisWeight_nonneg q) (productWeight_nonneg q n)
lemma productWeight_majorizes_regularized (q : ℝ) (hq : 0 ≤ q)
    (d : ℕ) (k : Fin d → ℤ) :
    (∏ i : Fin d, regularizedAxisWeight q (k i)) ≤ productWeight q d k := by
  rw [productWeight_eq_prod]
  apply Finset.prod_le_prod
  · intro i hi
    exact regularizedAxisWeight_nonneg q (k i)
  · intro i hi
    exact regularizedAxisWeight_le_axisWeight q hq (k i)
lemma coord_norm_le_pi {d : ℕ} (k : Fin d → ℤ) (i : Fin d) :
    ‖(k i : ℝ)‖ ≤ ‖k‖ := by
  have h := norm_le_pi_norm k i
  simpa [Int.norm_eq_abs, Int.cast_abs, Real.norm_eq_abs] using h
lemma radial_weight_le_regularized_product {d : ℕ} (hd : 0 < d)
    (p : ℝ) (hp : 0 ≤ p) (k : Fin d → ℤ) :
    (1 + ‖k‖) ^ (-p) ≤
      ∏ i : Fin d, regularizedAxisWeight (p / (d : ℝ)) (k i) := by
  let M : ℝ := 1 + ‖k‖
  have hM : 0 < M := by dsimp [M]; positivity
  have hcoord (i : Fin d) : 1 + ‖(k i : ℝ)‖ ≤ M := by
    dsimp [M]
    exact add_le_add_right (coord_norm_le_pi k i) 1
  have hexp : -p / (d : ℝ) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact_mod_cast hd.le
  have hfactor (i : Fin d) : M ^ (-p / (d : ℝ)) ≤
      regularizedAxisWeight (p / (d : ℝ)) (k i) := by
    simp only [regularizedAxisWeight]
    have h := Real.rpow_le_rpow_of_nonpos (by positivity) (hcoord i) hexp
    have he : -p / (d : ℝ) = -(p / (d : ℝ)) := by ring
    rw [← he]
    exact h
  have hprod : (∏ _i : Fin d, M ^ (-p / (d : ℝ))) ≤
      ∏ i : Fin d, regularizedAxisWeight (p / (d : ℝ)) (k i) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact Real.rpow_nonneg hM.le _
    · intro i hi
      exact hfactor i
  have hleft : (∏ _i : Fin d, M ^ (-p / (d : ℝ))) = M ^ (-p) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    calc
      (M ^ (-p / (d : ℝ))) ^ d = (M ^ (-p / (d : ℝ))) ^ (d : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = M ^ ((-p / (d : ℝ)) * (d : ℝ)) := (Real.rpow_mul hM.le _ _).symm
      _ = M ^ (-p) := by congr 1; field_simp
  change M ^ (-p) ≤ _
  rw [← hleft]
  exact hprod
lemma radial_weight_le_productWeight {d : ℕ} (hd : 0 < d)
    (p : ℝ) (hp : 0 ≤ p) (k : Fin d → ℤ) :
    (1 + ‖k‖) ^ (-p) ≤ productWeight (p / (d : ℝ)) d k := by
  exact (radial_weight_le_regularized_product hd p hp k).trans
    (productWeight_majorizes_regularized (p / (d : ℝ)) (by positivity) d k)

lemma target_weight_summable :
    Summable (fun k : Fin 122409 → ℤ => (1 + ‖k‖) ^ (-2 * (61206 : ℝ))) := by
  let p : ℝ := 2 * (61206 : ℝ)
  let q : ℝ := p / (122409 : ℝ)
  have hq : 1 < q := by norm_num [p, q]
  apply Summable.of_nonneg_of_le
  · intro k
    have hk : 0 ≤ ‖k‖ := norm_nonneg k
    exact Real.rpow_nonneg (by linarith) _
  · intro k
    simpa [p, q] using radial_weight_le_productWeight
      (d := 122409) (by norm_num) p (by positivity) k
  · simpa [p, q] using productWeight_summable q hq 122409

lemma energy_weight_summable :
    Summable (fun k : Fin 122409 → ℤ => (1 + ‖k‖) ^ (-2 * (61205 : ℝ))) := by
  let p : ℝ := 2 * (61205 : ℝ)
  let q : ℝ := p / (122409 : ℝ)
  have hq : 1 < q := by norm_num [p, q]
  apply Summable.of_nonneg_of_le
  · intro k
    have hk : 0 ≤ ‖k‖ := norm_nonneg k
    exact Real.rpow_nonneg (by linarith) _
  · intro k
    simpa [p, q] using radial_weight_le_productWeight
      (d := 122409) (by norm_num) p (by positivity) k
  · simpa [p, q] using productWeight_summable q hq 122409

#print axioms target_weight_summable
#print axioms energy_weight_summable
end Pphi2Clean.DimensionFreeProbe
