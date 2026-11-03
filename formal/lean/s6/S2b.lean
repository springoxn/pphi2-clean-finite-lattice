import S6Isserlis.S2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# S2b — distributional Euclidean invariance of the Schwinger functions

`S2.lean` proves the *pointwise* invariance of `S_n` under the Euclidean group `E(4)`
(`Sn_E4_invariant`). The paper (`thm:os2i`) needs the corresponding statement at the level of
the *distribution*: the Schwinger functions, viewed as a distribution, are invariant under
`E(4)`. The missing ingredient is the measure-theoretic change-of-variables step.

This file provides:

* the diagonal action `E4.famAct` of `E4` on families of `n` points, its two-sided inverse
  `E4.famInv`, and the associated `MeasurableEquiv`;
* `E4.measurePreserving_famAct`: `famAct g` preserves Lebesgue measure (= additive Haar
  measure) on `(Fin n → Fin 4 → ℝ)`;
* `Sn_integral_E4_invariant`: the distributional change-of-variables identity
  `∫ x, S_n(x) • φ(g⁻¹ x) = ∫ x, S_n(x) • φ(x)`,
  and its counterpart with `famAct`.

The measure-preservation of `famAct g` is reduced, via `Measure.pi_map_pi`, to
measure-preservation of `E4.act` on `ℝ⁴ = Fin 4 → ℝ`. Note `Fin 4 → ℝ` carries the *sup* norm
(not an inner-product norm), so `LinearIsometryEquiv.measurePreserving` does not apply; instead
we use that a linear isometry of `Fin 4 → ℝ` preserves the closed unit ball, so its determinant
has absolute value `1`, and `Real.map_linearMap_volume_pi_eq_smul_volume_pi`.
-/

noncomputable section

open scoped BigOperators
open Classical
open MeasureTheory MeasureTheory.Measure

namespace Schwinger

namespace E4

variable {n : ℕ}

/-- Diagonal action of the Euclidean group on families of `n` points. -/
def famAct (g : E4) (x : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ := fun i => g.act (x i)

/-- The two-sided inverse of `famAct g`, given by applying `g.lin.symm` after undoing the
translation. -/
def famInv (g : E4) (x : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => g.lin.symm (x i - g.shift)

@[simp] lemma famAct_apply (g : E4) (x : Fin n → Fin 4 → ℝ) (i : Fin n) :
    famAct g x i = g.act (x i) := rfl

@[simp] lemma famInv_apply (g : E4) (x : Fin n → Fin 4 → ℝ) (i : Fin n) :
    famInv g x i = g.lin.symm (x i - g.shift) := rfl

/-- `famInv g` is a left inverse of `famAct g`. -/
lemma famAct_left_inv (g : E4) (x : Fin n → Fin 4 → ℝ) : famInv g (famAct g x) = x := by
  funext i
  show g.lin.symm (g.lin (x i) + g.shift - g.shift) = x i
  rw [add_sub_cancel_right, LinearIsometryEquiv.symm_apply_apply]

/-- `famInv g` is a right inverse of `famAct g`. -/
lemma famAct_right_inv (g : E4) (x : Fin n → Fin 4 → ℝ) : famAct g (famInv g x) = x := by
  funext i
  show g.lin (g.lin.symm (x i - g.shift)) + g.shift = x i
  rw [LinearIsometryEquiv.apply_symm_apply, sub_add_cancel]

/-- The action `E4.act g` on `ℝ⁴ = Fin 4 → ℝ` is measurable. -/
lemma measurable_act (g : E4) : Measurable (g.act) := by
  have h : g.act = fun x : Fin 4 → ℝ => g.lin x + g.shift := rfl
  rw [h]
  exact g.lin.continuous.measurable.add measurable_const

/-- The diagonal action `famAct g` is measurable. -/
lemma measurable_famAct (g : E4) : Measurable (famAct (n := n) g) :=
  measurable_pi_lambda _
    (fun i => (measurable_act g).comp (measurable_pi_apply i))

/-- The inverse `famInv g` is measurable. -/
lemma measurable_famInv (g : E4) : Measurable (famInv (n := n) g) :=
  measurable_pi_lambda _
    (fun i => (g.lin.symm.continuous.measurable).comp
      ((measurable_pi_apply i).sub measurable_const))

/-- A linear isometry of `Fin 4 → ℝ` (with its sup norm) preserves Lebesgue measure. -/
lemma measurePreserving_lin (g : E4) :
    MeasurePreserving (g.lin) (volume : Measure (Fin 4 → ℝ)) volume := by
  have hdet : LinearMap.det (g.lin.toLinearEquiv.toLinearMap) ≠ 0 := by
    intro h
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h
    exact h (by rw [LinearMap.ker_eq_bot]; exact g.lin.injective)
  have hV : volume (Metric.closedBall (0 : Fin 4 → ℝ) 1) = 16 := by
    rw [MeasureTheory.volume_pi_closedBall (0 : Fin 4 → ℝ) (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [Pi.zero_apply, Real.volume_closedBall, mul_one, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  have hpre : (g.lin : (Fin 4 → ℝ) → (Fin 4 → ℝ)) ⁻¹' Metric.closedBall (0 : Fin 4 → ℝ) 1
      = Metric.closedBall (0 : Fin 4 → ℝ) 1 := by
    rw [LinearIsometryEquiv.preimage_closedBall]
    simp
  have hscale : (16 : ENNReal) =
      ENNReal.ofReal (abs ((LinearMap.det (g.lin.toLinearEquiv.toLinearMap))⁻¹)) * 16 := by
    have h := congrArg (fun μ : Measure (Fin 4 → ℝ) =>
        μ (Metric.closedBall (0 : Fin 4 → ℝ) 1))
      (Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := g.lin.toLinearEquiv.toLinearMap) hdet)
    simp only [LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv] at h
    rw [Measure.map_apply g.lin.continuous.measurable Metric.isClosed_closedBall.measurableSet,
      Measure.smul_apply] at h
    rw [hpre, hV] at h
    exact h
  have hc : ENNReal.ofReal (abs ((LinearMap.det (g.lin.toLinearEquiv.toLinearMap))⁻¹)) = 1 := by
    have h2 := congrArg ENNReal.toReal hscale.symm
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at h2
    have hc1 : abs ((LinearMap.det (g.lin.toLinearEquiv.toLinearMap))⁻¹) = 1 := by
      have h16 : (16 : ENNReal).toReal = 16 := by norm_num
      rw [h16] at h2
      nlinarith
    rw [hc1, ENNReal.ofReal_one]
  refine ⟨g.lin.continuous.measurable, ?_⟩
  have h : Measure.map (⇑(g.lin.toLinearEquiv.toLinearMap)) volume = volume := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := g.lin.toLinearEquiv.toLinearMap) hdet,
      hc, one_smul]
  simpa only [LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv] using h

/-- The single-point action `E4.act g` preserves Lebesgue measure on `Fin 4 → ℝ`. -/
lemma measurePreserving_act (g : E4) :
    MeasurePreserving (g.act) (volume : Measure (Fin 4 → ℝ)) volume := by
  have h : g.act = (fun y : Fin 4 → ℝ => y + g.shift) ∘ g.lin := rfl
  rw [h]
  exact (measurePreserving_add_right volume g.shift).comp (measurePreserving_lin g)

/-- **Measure preservation of the diagonal action.** `famAct g` preserves Lebesgue measure on
the space of families of `n` points. -/
lemma measurePreserving_famAct (g : E4) :
    MeasurePreserving (famAct (n := n) g) (volume : Measure (Fin n → Fin 4 → ℝ)) volume := by
  refine ⟨measurable_famAct g, ?_⟩
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin n => (volume : Measure (Fin 4 → ℝ)))
      (f := fun _ : Fin n => (g.act : (Fin 4 → ℝ) → (Fin 4 → ℝ)))
      (hμ := fun _ => by
        rw [MeasurePreserving.map_eq (measurePreserving_act g)]; infer_instance)
      (fun _ => (measurePreserving_act g).measurable.aemeasurable)
  rw [MeasurePreserving.map_eq (measurePreserving_act g)] at hpi
  rw [volume_pi]
  exact hpi

/-- The diagonal action as a measurable equivalence. -/
def famActMeasurableEquiv (g : E4) : (Fin n → Fin 4 → ℝ) ≃ᵐ (Fin n → Fin 4 → ℝ) where
  toEquiv :=
    { toFun := famAct g
      invFun := famInv g
      left_inv := famAct_left_inv g
      right_inv := famAct_right_inv g }
  measurable_toFun := measurable_famAct g
  measurable_invFun := measurable_famInv g

lemma coe_famActMeasurableEquiv (g : E4) :
    ⇑(famActMeasurableEquiv (n := n) g) = famAct g := rfl

end E4

/-- **Distributional Euclidean invariance of `S_n`.** The Schwinger function `S_n`, as a
distribution, is invariant under the Euclidean group `E(4)`: integrating against a test
function transported by `g⁻¹` gives the same result. -/
theorem Sn_integral_E4_invariant (m : ℝ) (n : ℕ) (g : E4)
    (φ : (Fin n → Fin 4 → ℝ) → ℝ) :
    (∫ x, Sn m n x * φ (E4.famInv g x)) = ∫ x, Sn m n x * φ x := by
  have hmp : MeasurePreserving
      (⇑(E4.famActMeasurableEquiv (n := n) g)) volume volume :=
    E4.measurePreserving_famAct g
  have hcv := hmp.integral_comp' (fun x => Sn m n x * φ (E4.famInv g x))
  simp only [E4.coe_famActMeasurableEquiv] at hcv
  have hpt : (fun y => Sn m n (E4.famAct g y) * φ (E4.famInv g (E4.famAct g y)))
      = fun y => Sn m n y * φ y := by
    funext y
    rw [show Sn m n (E4.famAct g y) = Sn m n y from Sn_E4_invariant m n g y,
      E4.famAct_left_inv]
  rw [hpt] at hcv
  exact hcv.symm

/-- The counterpart of `Sn_integral_E4_invariant` with `famAct` instead of `famInv`. -/
theorem Sn_integral_E4_invariant_famAct (m : ℝ) (n : ℕ) (g : E4)
    (φ : (Fin n → Fin 4 → ℝ) → ℝ) :
    (∫ x, Sn m n x * φ (E4.famAct g x)) = ∫ x, Sn m n x * φ x := by
  have hmp : MeasurePreserving
      (⇑(E4.famActMeasurableEquiv (n := n) g)) volume volume :=
    E4.measurePreserving_famAct g
  have hcv := hmp.integral_comp' (fun x => Sn m n x * φ x)
  simp only [E4.coe_famActMeasurableEquiv] at hcv
  have hpt : (fun y => Sn m n (E4.famAct g y) * φ (E4.famAct g y))
      = fun y => Sn m n y * φ (E4.famAct g y) := by
    funext y
    rw [show Sn m n (E4.famAct g y) = Sn m n y from Sn_E4_invariant m n g y]
  rw [hpt] at hcv
  exact hcv

end Schwinger
