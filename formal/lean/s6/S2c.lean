import S6Isserlis.S2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# S2c — OS2 invariance on the *faithful* Euclidean space

`S2.lean` / `S2b.lean` formalize the OS2 invariance of the Schwinger functions using
`Fin 4 → ℝ`.  That type carries the **sup norm** (`Pi.instNorm`), so
`LinearIsometryEquiv (Fin 4 → ℝ) (Fin 4 → ℝ)` is the sup-norm isometry group, *not* the
Euclidean orthogonal group `O(4)` that the paper's OS2 statement refers to.

This file redoes the geometric part on `EuclideanSpace ℝ (Fin 4)`, Mathlib's type synonym for
`ℝ⁴` equipped with the ℓ² inner product.  Here `LinearIsometryEquiv` really is `O(4)`, and
`LinearIsometryEquiv.measurePreserving` applies directly — no determinant / closed-ball
detour as in `S2b.lean`.

Nothing in `S2.lean` / `S2b.lean` is modified; the combinatorial layer (`IsPerfectMatching`,
`matchings`, `Sym2`) is reused verbatim from `S2.lean`.
-/

noncomputable section

open scoped BigOperators
open Classical
open MeasureTheory MeasureTheory.Measure

namespace Schwinger

variable {n : ℕ}

/-! ## The Euclidean two-point kernel -/

/-- Definition-level Euclidean two-point kernel on the honest Euclidean space
`EuclideanSpace ℝ (Fin 4)` (ℓ² inner product, so the linear isometries are `O(4)`).  The
kernel itself only depends on the scalar norm, hence `aIntegral` from `S1a.lean` is reused
unchanged. -/
def twoPointE (m : ℝ) (x y : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  (1 / (16 * Real.pi ^ 2)) * aIntegral m ‖x - y‖

/-- The Euclidean two-point kernel is symmetric. -/
theorem twoPointE_symm (m : ℝ) (x y : EuclideanSpace ℝ (Fin 4)) :
    twoPointE m x y = twoPointE m y x := by
  unfold twoPointE
  rw [norm_sub_rev]

/-! ## The Euclidean group -/

/-- Euclidean transformation of `EuclideanSpace ℝ (Fin 4)`: an orthogonal transformation
(`LinearIsometryEquiv` of the inner-product space, i.e. an element of `O(4)`) followed by a
translation. -/
structure E4E where
  lin : (EuclideanSpace ℝ (Fin 4)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 4))
  shift : EuclideanSpace ℝ (Fin 4)

namespace E4E

/-- Action of `E4E` on Euclidean `ℝ⁴`. -/
def act (g : E4E) (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  g.lin x + g.shift

end E4E

/-- Invariance of `twoPointE` under a linear isometry of the Euclidean space.  This is where the
ℓ² structure is used: `Q.norm_map` is the statement `‖Q z‖ = ‖z‖` for the Euclidean norm. -/
theorem twoPointE_lin_invariant (m : ℝ)
    (Q : (EuclideanSpace ℝ (Fin 4)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 4)))
    (x y : EuclideanSpace ℝ (Fin 4)) :
    twoPointE m (Q x) (Q y) = twoPointE m x y := by
  unfold twoPointE
  rw [← Q.map_sub, Q.norm_map]

/-- Invariance of `twoPointE` under the orthogonal part of a Euclidean transformation. -/
theorem twoPointE_orth_invariant (m : ℝ) (g : E4E) (x y : EuclideanSpace ℝ (Fin 4)) :
    twoPointE m (g.lin x) (g.lin y) = twoPointE m x y :=
  twoPointE_lin_invariant m g.lin x y

/-- Invariance of `twoPointE` under a common translation. -/
theorem twoPointE_trans_invariant (m : ℝ) (v x y : EuclideanSpace ℝ (Fin 4)) :
    twoPointE m (x + v) (y + v) = twoPointE m x y := by
  unfold twoPointE
  rw [show x + v - (y + v) = x - y by abel]

/-- **OS2 invariance of the Euclidean two-point kernel** under the Euclidean group `E(4)`,
combining the orthogonal and translation invariances. -/
theorem twoPointE_E4E_invariant (m : ℝ) (g : E4E) (x y : EuclideanSpace ℝ (Fin 4)) :
    twoPointE m (g.act x) (g.act y) = twoPointE m x y := by
  rw [E4E.act, E4E.act, twoPointE_trans_invariant m g.shift (g.lin x) (g.lin y),
    twoPointE_orth_invariant m g x y]

/-! ## Measure preservation

`EuclideanSpace ℝ (Fin 4)` is an inner-product space, so
`LinearIsometryEquiv.measurePreserving` applies *directly*. -/

namespace E4E

/-- The action `E4E.act g` on `EuclideanSpace ℝ (Fin 4)` is measurable. -/
lemma measurable_actE (g : E4E) : Measurable (g.act) := by
  have h : g.act = fun x : EuclideanSpace ℝ (Fin 4) => g.lin x + g.shift := rfl
  rw [h]
  exact g.lin.continuous.measurable.add measurable_const

/-- A linear isometry of the Euclidean space preserves Lebesgue measure.  Direct application of
`LinearIsometryEquiv.measurePreserving`; no determinant computation needed. -/
lemma measurePreserving_linE (g : E4E) :
    MeasurePreserving (g.lin) (volume : Measure (EuclideanSpace ℝ (Fin 4))) volume :=
  LinearIsometryEquiv.measurePreserving g.lin

/-- The single-point Euclidean action `g.act` preserves Lebesgue measure: a measure-preserving
orthogonal map followed by a measure-preserving translation. -/
lemma measurePreserving_actE (g : E4E) :
    MeasurePreserving (g.act) (volume : Measure (EuclideanSpace ℝ (Fin 4))) volume := by
  have h : g.act = (fun y : EuclideanSpace ℝ (Fin 4) => y + g.shift) ∘ g.lin := rfl
  rw [h]
  exact (measurePreserving_add_right volume g.shift).comp (measurePreserving_linE g)

/-- Diagonal action of the Euclidean group on families of `n` points. -/
def famActE (g : E4E) (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    Fin n → EuclideanSpace ℝ (Fin 4) := fun i => g.act (x i)

/-- The two-sided inverse of `famActE g`. -/
def famInvE (g : E4E) (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    Fin n → EuclideanSpace ℝ (Fin 4) := fun i => g.lin.symm (x i - g.shift)

@[simp] lemma famActE_apply (g : E4E) (x : Fin n → EuclideanSpace ℝ (Fin 4)) (i : Fin n) :
    famActE g x i = g.act (x i) := rfl

@[simp] lemma famInvE_apply (g : E4E) (x : Fin n → EuclideanSpace ℝ (Fin 4)) (i : Fin n) :
    famInvE g x i = g.lin.symm (x i - g.shift) := rfl

/-- `famInvE g` is a left inverse of `famActE g`. -/
lemma famActE_left_inv (g : E4E) (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    famInvE g (famActE g x) = x := by
  funext i
  show g.lin.symm (g.lin (x i) + g.shift - g.shift) = x i
  rw [add_sub_cancel_right, LinearIsometryEquiv.symm_apply_apply]

/-- `famInvE g` is a right inverse of `famActE g`. -/
lemma famActE_right_inv (g : E4E) (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    famActE g (famInvE g x) = x := by
  funext i
  show g.lin (g.lin.symm (x i - g.shift)) + g.shift = x i
  rw [LinearIsometryEquiv.apply_symm_apply, sub_add_cancel]

/-- The diagonal action is measurable. -/
lemma measurable_famActE (g : E4E) : Measurable (famActE (n := n) g) :=
  measurable_pi_lambda _ (fun i => (measurable_actE g).comp (measurable_pi_apply i))

/-- The inverse of the diagonal action is measurable. -/
lemma measurable_famInvE (g : E4E) : Measurable (famInvE (n := n) g) :=
  measurable_pi_lambda _ (fun i => (g.lin.symm.continuous.measurable).comp
    ((measurable_pi_apply i).sub measurable_const))

/-- **Measure preservation of the diagonal action**, reduced to the single-point case via
`Measure.pi_map_pi`. -/
lemma measurePreserving_famActE (g : E4E) :
    MeasurePreserving (famActE (n := n) g)
      (volume : Measure (Fin n → EuclideanSpace ℝ (Fin 4))) volume := by
  refine ⟨measurable_famActE g, ?_⟩
  rw [volume_pi]
  have hmp := measurePreserving_actE g
  have hpi := Measure.pi_map_pi
      (μ := fun _ : Fin n => (volume : Measure (EuclideanSpace ℝ (Fin 4))))
      (f := fun _ : Fin n => (g.act : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)))
      (hμ := fun _ => by rw [MeasurePreserving.map_eq hmp]; infer_instance)
      (fun _ => hmp.measurable.aemeasurable)
  rw [MeasurePreserving.map_eq hmp] at hpi
  exact hpi

/-- The diagonal action as a measurable equivalence. -/
def famActEMeasurableEquiv (g : E4E) :
    (Fin n → EuclideanSpace ℝ (Fin 4)) ≃ᵐ (Fin n → EuclideanSpace ℝ (Fin 4)) where
  toEquiv :=
    { toFun := famActE g
      invFun := famInvE g
      left_inv := famActE_left_inv g
      right_inv := famActE_right_inv g }
  measurable_toFun := measurable_famActE g
  measurable_invFun := measurable_famInvE g

lemma coe_famActEMeasurableEquiv (g : E4E) :
    ⇑(famActEMeasurableEquiv (n := n) g) = famActE g := rfl

end E4E

/-! ## Schwinger functions on the Euclidean space

The matching combinatorics (`IsPerfectMatching`, `matchings`, `Sym2`) is reused verbatim from
`S2.lean`; only the geometric factor changes. -/

/-- The pairing factor of one unordered pair, well defined by the symmetry of `twoPointE`. -/
def pairFactorE (m : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin 4)) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun a b => twoPointE m (x a) (x b), fun a b => twoPointE_symm m (x a) (x b)⟩

/-- A pairing product `∏_{pairs} C_m(x_i − x_j)`. -/
def pairingProdE (m : ℝ) (M : Finset (Sym2 (Fin n)))
    (x : Fin n → EuclideanSpace ℝ (Fin 4)) : ℝ :=
  ∏ e ∈ M, pairFactorE m x e

/-- The Schwinger function `S_n` on the Euclidean space, as the sum of pairing products over
all perfect matchings. -/
def SnE (m : ℝ) (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin 4)) : ℝ :=
  ∑ M ∈ matchings n, pairingProdE m M x

/-- The pairing factor is invariant under a linear isometry applied coordinatewise. -/
lemma pairFactorE_orth (m : ℝ)
    (Q : (EuclideanSpace ℝ (Fin 4)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 4)))
    (x : Fin n → EuclideanSpace ℝ (Fin 4)) (e : Sym2 (Fin n)) :
    pairFactorE m (fun i => Q (x i)) e = pairFactorE m x e := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [pairFactorE, Sym2.lift_mk]
    exact twoPointE_lin_invariant m Q (x a) (x b)

/-- The pairing factor is invariant under a common translation. -/
lemma pairFactorE_trans (m : ℝ) (v : EuclideanSpace ℝ (Fin 4))
    (x : Fin n → EuclideanSpace ℝ (Fin 4)) (e : Sym2 (Fin n)) :
    pairFactorE m (fun i => x i + v) e = pairFactorE m x e := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [pairFactorE, Sym2.lift_mk]
    exact twoPointE_trans_invariant m v (x a) (x b)

/-- Pairing products are invariant under a coordinatewise linear isometry. -/
lemma pairingProdE_orth (m : ℝ)
    (Q : (EuclideanSpace ℝ (Fin 4)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 4)))
    (M : Finset (Sym2 (Fin n))) (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    pairingProdE m M (fun i => Q (x i)) = pairingProdE m M x := by
  unfold pairingProdE
  exact Finset.prod_congr rfl (fun e _ => pairFactorE_orth m Q x e)

/-- Pairing products are invariant under a common translation. -/
lemma pairingProdE_trans (m : ℝ) (v : EuclideanSpace ℝ (Fin 4))
    (M : Finset (Sym2 (Fin n))) (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    pairingProdE m M (fun i => x i + v) = pairingProdE m M x := by
  unfold pairingProdE
  exact Finset.prod_congr rfl (fun e _ => pairFactorE_trans m v x e)

/-- `S_n` is invariant under a coordinatewise linear isometry. -/
lemma SnE_orth (m : ℝ) (n : ℕ)
    (Q : (EuclideanSpace ℝ (Fin 4)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 4)))
    (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    SnE m n (fun i => Q (x i)) = SnE m n x := by
  unfold SnE
  exact Finset.sum_congr rfl (fun M _ => pairingProdE_orth m Q M x)

/-- `S_n` is invariant under a common translation. -/
lemma SnE_trans (m : ℝ) (n : ℕ) (v : EuclideanSpace ℝ (Fin 4))
    (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    SnE m n (fun i => x i + v) = SnE m n x := by
  unfold SnE
  exact Finset.sum_congr rfl (fun M _ => pairingProdE_trans m v M x)

/-- **OS2 algebraic core, faithful version.** The Schwinger function `S_n` on the Euclidean
space is invariant under the Euclidean group `E(4)` acting diagonally. -/
theorem SnE_E4E_invariant (m : ℝ) (n : ℕ) (g : E4E)
    (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    SnE m n (fun i => g.act (x i)) = SnE m n x := by
  rw [show (fun i => g.act (x i)) = (fun i => g.lin (x i) + g.shift) from rfl,
    SnE_trans m n g.shift (fun i => g.lin (x i)), SnE_orth m n g.lin x]

/-- `SnE` is invariant along the diagonal action, in the `famActE` spelling. -/
lemma SnE_famActE (m : ℝ) (n : ℕ) (g : E4E) (x : Fin n → EuclideanSpace ℝ (Fin 4)) :
    SnE m n (E4E.famActE g x) = SnE m n x :=
  SnE_E4E_invariant m n g x

/-- **Distributional OS2 invariance on the Euclidean space.** The Schwinger function `S_n`, as a
distribution, is invariant under `E(4)`: integrating against a test function transported by
`g⁻¹` gives the same result.  The proof is the change of variables along the
measure-preserving diagonal action `famActE g`. -/
theorem SnE_integral_E4_invariant (m : ℝ) (n : ℕ) (g : E4E)
    (φ : (Fin n → EuclideanSpace ℝ (Fin 4)) → ℝ) :
    (∫ x, SnE m n x * φ (E4E.famInvE g x)) = ∫ x, SnE m n x * φ x := by
  have hmp : MeasurePreserving
      (⇑(E4E.famActEMeasurableEquiv (n := n) g)) volume volume :=
    E4E.measurePreserving_famActE g
  have hcv := hmp.integral_comp' (fun x => SnE m n x * φ (E4E.famInvE g x))
  simp only [E4E.coe_famActEMeasurableEquiv] at hcv
  have hpt : (fun y => SnE m n (E4E.famActE g y) * φ (E4E.famInvE g (E4E.famActE g y)))
      = fun y => SnE m n y * φ y := by
    funext y
    rw [show SnE m n (E4E.famActE g y) = SnE m n y from SnE_famActE m n g y,
      E4E.famActE_left_inv]
  rw [hpt] at hcv
  exact hcv.symm

end Schwinger
