import S6Isserlis.S4
import Mathlib.Data.Sym.Sym2

/-!
# S2 — OS2 algebraic invariance core

Lifts the two-point symmetry core of `S4.lean` to the Euclidean group `E(4)` and to
Schwinger pairing products, giving the algebraic seed of the distribution-level
Euclidean invariance of the Schwinger functions (paper `thm:os2i`, `lem:sn-pointwise`).
-/

noncomputable section

open scoped BigOperators
open Classical

namespace Schwinger

/-- Euclidean transformation of `ℝ⁴`: a linear isometry followed by a translation. -/
structure E4 where
  lin : (Fin 4 → ℝ) ≃ₗᵢ[ℝ] (Fin 4 → ℝ)
  shift : Fin 4 → ℝ

namespace E4

/-- Action of `E4` on `ℝ⁴`. -/
def act (g : E4) (x : Fin 4 → ℝ) : Fin 4 → ℝ := g.lin x + g.shift

end E4

/-- Invariance of the two-point kernel under the Euclidean group, combining the
orthogonal and translation invariances of `S4.lean`. -/
theorem E4_twoPoint_invariant (m : ℝ) (g : E4) (x y : Fin 4 → ℝ) :
    twoPoint m (g.act x) (g.act y) = twoPoint m x y := by
  rw [E4.act, E4.act, s4_translation_invariant m (g.lin x) (g.lin y) g.shift,
      s4_orthogonal_invariant m g.lin x y]

variable {n : ℕ}

/-- A perfect matching of `Fin n`: a set of unordered pairs covering every vertex
exactly once.  The first conjunct excludes degenerate "loops" `Sym2.mk a a`: without it
the unique-partner condition is still satisfied after adjoining any loop, so the set
would not be a partition into pairs (`#(matchings 4)` would be `48` instead of `3`). -/
def IsPerfectMatching (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag) ∧ ∀ a : Fin n, ∃! b : Fin n, b ≠ a ∧ Sym2.mk a b ∈ M

/-- The finite set of all perfect matchings of `Fin n`. -/
def matchings (n : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  Finset.univ.filter (IsPerfectMatching (n := n))

/-- The pairing factor of one unordered pair, well defined because the two-point
kernel is symmetric. -/
def pairFactor (m : ℝ) (x : Fin n → Fin 4 → ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun a b => twoPoint m (x a) (x b), fun a b => s4_symmetric m (x a) (x b)⟩

/-- A pairing product `∏_{pairs} C_m(x_i − x_j)`. -/
def pairingProd (m : ℝ) (M : Finset (Sym2 (Fin n))) (x : Fin n → Fin 4 → ℝ) : ℝ :=
  ∏ e ∈ M, pairFactor m x e

/-- The Schwinger function `S_n`, as the sum of pairing products over all
perfect matchings. -/
def Sn (m : ℝ) (n : ℕ) (x : Fin n → Fin 4 → ℝ) : ℝ :=
  ∑ M ∈ matchings n, pairingProd m M x

/-- The pairing factor is invariant under a linear isometry applied coordinatewise. -/
lemma pairFactor_orth (m : ℝ) (Q : (Fin 4 → ℝ) ≃ₗᵢ[ℝ] (Fin 4 → ℝ))
    (x : Fin n → Fin 4 → ℝ) (e : Sym2 (Fin n)) :
    pairFactor m (fun i => Q (x i)) e = pairFactor m x e := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [pairFactor, Sym2.lift_mk]
    exact s4_orthogonal_invariant m Q (x a) (x b)

/-- The pairing factor is invariant under a common translation. -/
lemma pairFactor_trans (m : ℝ) (v : Fin 4 → ℝ)
    (x : Fin n → Fin 4 → ℝ) (e : Sym2 (Fin n)) :
    pairFactor m (fun i => x i + v) e = pairFactor m x e := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [pairFactor, Sym2.lift_mk]
    exact s4_translation_invariant m (x a) (x b) v

/-- Pairing products are invariant under a coordinatewise linear isometry. -/
lemma pairingProd_orth (m : ℝ) (Q : (Fin 4 → ℝ) ≃ₗᵢ[ℝ] (Fin 4 → ℝ))
    (M : Finset (Sym2 (Fin n))) (x : Fin n → Fin 4 → ℝ) :
    pairingProd m M (fun i => Q (x i)) = pairingProd m M x := by
  unfold pairingProd
  exact Finset.prod_congr rfl (fun e _ => pairFactor_orth m Q x e)

/-- Pairing products are invariant under a common translation. -/
lemma pairingProd_trans (m : ℝ) (v : Fin 4 → ℝ)
    (M : Finset (Sym2 (Fin n))) (x : Fin n → Fin 4 → ℝ) :
    pairingProd m M (fun i => x i + v) = pairingProd m M x := by
  unfold pairingProd
  exact Finset.prod_congr rfl (fun e _ => pairFactor_trans m v x e)

/-- The Schwinger function `S_n` is invariant under a coordinatewise linear isometry. -/
lemma Sn_orth (m : ℝ) (n : ℕ) (Q : (Fin 4 → ℝ) ≃ₗᵢ[ℝ] (Fin 4 → ℝ))
    (x : Fin n → Fin 4 → ℝ) :
    Sn m n (fun i => Q (x i)) = Sn m n x := by
  unfold Sn
  exact Finset.sum_congr rfl (fun M _ => pairingProd_orth m Q M x)

/-- The Schwinger function `S_n` is invariant under a common translation. -/
lemma Sn_trans (m : ℝ) (n : ℕ) (v : Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ) :
    Sn m n (fun i => x i + v) = Sn m n x := by
  unfold Sn
  exact Finset.sum_congr rfl (fun M _ => pairingProd_trans m v M x)

/-- **OS2 algebraic core.** The Schwinger function `S_n` is invariant under the
Euclidean group `E(4)` acting diagonally. -/
theorem Sn_E4_invariant (m : ℝ) (n : ℕ) (g : E4) (x : Fin n → Fin 4 → ℝ) :
    Sn m n (fun i => g.act (x i)) = Sn m n x := by
  have h : (fun i => g.act (x i)) = (fun i => g.lin (x i) + g.shift) := by
    funext i; rw [E4.act]
  rw [h, Sn_trans m n g.shift (fun i => g.lin (x i)), Sn_orth m n g.lin x]

end Schwinger

-- 2026-09-18: this file was previously compiled into a stale olean (pre-fix definition, 2026-09-13) because the root module did not import it. See S6Isserlis.lean.
