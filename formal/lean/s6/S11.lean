import S6Isserlis.S7
import S6Isserlis.S8

/-!
# S11 — the pairing multilinear form `Ψ = Σ_M ∏_{e ∈ M} B(·,·)`

P3b-i (i): the pairing sum `Ψ(v) = Σ_{M ∈ matchings n} ∏_{e ∈ M} B(v_{e.1}, v_{e.2})` of `S2.lean`
is built as a **symmetric multilinear map** on `Fin n → E`, for an arbitrary symmetric bilinear
form `B` on `E`.  This is the algebraic object whose diagonal value is
`#(matchings n) · (B v v)^{n/2}`; it is the right-hand side of the finite-dimensional Gauss–Wick
theorem proved in `S12.lean`.

`S2.lean`'s own `pairFactor`/`pairingProd` are *not* multilinear in the configuration `x`
(they are built on `twoPoint m`, which depends on `‖xᵢ - xⱼ‖`); only their combinatorial skeleton
(`matchings`, the `Sym2`-indexed product) is reused here, with `C(·,·)` replaced by a general
symmetric bilinear form.  This is the object that the paper's pairing sum really is.

## Contents

* `pairFactorB`, `prodB` — the pairing factor and pairing product;
* `partner`, `partnerPair` — the unique partner of a vertex in a perfect matching;
* `prodB_update_add` / `prodB_update_smul` — `prodB` is linear in each slot;
* `pairingML`, `pairingML_isSymm` — the pairing sum as a symmetric `MultilinearMap`;
* `card_mul_two_of_isPerfectMatching` — a perfect matching of `Fin n` has `n / 2` pairs
  (hence `matchings n = ∅` for odd `n`);
* `pairingML_const` — the diagonal value `#(matchings n) · (B v v)^{n/2}`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators
open Classical

namespace Schwinger

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {n : ℕ}
-- The decidability instance is kept as a variable so that `Function.update` in the statements
-- below matches the (bound) instance appearing in `MultilinearMap`'s defining fields.
variable [DecidableEq (Fin n)]
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ u v : E, B u v = B v u)

/-! ### The pairing factor and the pairing product -/

/-- The pairing factor of one unordered pair for a bilinear form `B`, well defined because `B` is
symmetric. -/
def pairFactorB (v : Fin n → E) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun a c => B (v a) (v c), fun a c => hB (v a) (v c)⟩

@[simp]
lemma pairFactorB_mk (v : Fin n → E) (a c : Fin n) :
    pairFactorB B hB v (Sym2.mk a c) = B (v a) (v c) := by
  unfold pairFactorB
  exact Sym2.lift_mk _ a c

/-- The pairing product `∏_{e ∈ M} B(v_{e.1}, v_{e.2})` of a set `M` of unordered pairs. -/
def prodB (M : Finset (Sym2 (Fin n))) (v : Fin n → E) : ℝ :=
  ∏ e ∈ M, pairFactorB B hB v e

/-- The pairing factor does not see a slot that the pair does not contain. -/
lemma pairFactorB_update_of_notMem (v : Fin n → E) (i : Fin n) (w : E) {e : Sym2 (Fin n)}
    (he : i ∉ e) :
    pairFactorB B hB (Function.update v i w) e = pairFactorB B hB v e := by
  induction e using Sym2.ind with
  | h a c =>
    rw [Sym2.mem_iff] at he
    simp only [not_or] at he
    obtain ⟨hia, hic⟩ := he
    rw [pairFactorB_mk, pairFactorB_mk,
      Function.update_of_ne (Ne.symm hia) w v, Function.update_of_ne (Ne.symm hic) w v]

/-- The pairing factor on the diagonal is `B v v`. -/
lemma pairFactorB_const (v : E) (e : Sym2 (Fin n)) :
    pairFactorB B hB (fun _ : Fin n => v) e = B v v := by
  induction e using Sym2.ind with
  | h a c => rw [pairFactorB_mk]

/-- The pairing product on the diagonal is `(B v v)^{#M}`. -/
lemma prodB_const (M : Finset (Sym2 (Fin n))) (v : E) :
    prodB B hB M (fun _ : Fin n => v) = (B v v) ^ M.card := by
  unfold prodB
  trans ∏ _e ∈ M, (B v v)
  · exact Finset.prod_congr rfl fun e _ => pairFactorB_const B hB v e
  · rw [Finset.prod_const]

/-! ### The partner of a vertex in a perfect matching -/

/-- The unique partner of a vertex in a perfect matching (chosen from the existence part of
`IsPerfectMatching`). -/
def partner (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (i : Fin n) : Fin n :=
  Classical.choose (hM.2 i)

/-- The defining properties of `partner`, together with its uniqueness. -/
lemma partner_spec (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (i : Fin n) :
    (partner M hM i ≠ i ∧ Sym2.mk i (partner M hM i) ∈ M) ∧
      ∀ b : Fin n, (b ≠ i ∧ Sym2.mk i b ∈ M) → b = partner M hM i :=
  Classical.choose_spec (hM.2 i)

lemma partner_ne (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (i : Fin n) :
    partner M hM i ≠ i :=
  (partner_spec M hM i).1.1

lemma partner_mem (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (i : Fin n) :
    Sym2.mk i (partner M hM i) ∈ M :=
  (partner_spec M hM i).1.2

/-- `partner` is the unique vertex joined to `i` inside `M`. -/
lemma eq_partner (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (i : Fin n) {b : Fin n}
    (hb : b ≠ i) (hm : Sym2.mk i b ∈ M) : b = partner M hM i :=
  (partner_spec M hM i).2 b ⟨hb, hm⟩

/-- The pair of `M` containing the vertex `i`. -/
def partnerPair (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (i : Fin n) :
    Sym2 (Fin n) :=
  Sym2.mk i (partner M hM i)

lemma partnerPair_mem (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (i : Fin n) :
    partnerPair M hM i ∈ M :=
  partner_mem M hM i

lemma partnerPair_left (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (i : Fin n) :
    i ∈ partnerPair M hM i :=
  Sym2.mem_mk_left i (partner M hM i)

/-- The pair of `M` containing `i` is unique. -/
lemma eq_partnerPair_of_mem (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M)
    {e : Sym2 (Fin n)} (he : e ∈ M) {i : Fin n} (hi : i ∈ e) : e = partnerPair M hM i := by
  obtain ⟨b, hbne, hbe⟩ := exists_mk_of_mem (hM.1 e he) hi
  have hmem : Sym2.mk i b ∈ M := hbe ▸ he
  rw [hbe, eq_partner M hM i hbne hmem, partnerPair]

/-! ### Linearity of `prodB` in one slot -/

/-- Splitting off the pair of `i`: `prodB` is `B w (v (partner i))` times a product that does not
depend on the value at slot `i`. -/
lemma prodB_eq_mul_erase (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M)
    (v : Fin n → E) (i : Fin n) (w : E) :
    prodB B hB M (Function.update v i w) =
      B w (v (partner M hM i)) *
        ∏ e ∈ M.erase (partnerPair M hM i), pairFactorB B hB v e := by
  have hp : partnerPair M hM i ∈ M := partnerPair_mem M hM i
  unfold prodB
  rw [← Finset.mul_prod_erase M (fun e => pairFactorB B hB (Function.update v i w) e) hp]
  have hfirst : pairFactorB B hB (Function.update v i w) (partnerPair M hM i)
      = B w (v (partner M hM i)) := by
    rw [partnerPair, pairFactorB_mk]
    simp [partner_ne M hM i]
  have hrest : (∏ e ∈ M.erase (partnerPair M hM i),
        pairFactorB B hB (Function.update v i w) e)
      = ∏ e ∈ M.erase (partnerPair M hM i), pairFactorB B hB v e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hie : i ∉ e := fun hie =>
      (Finset.mem_erase.mp he).1
        (eq_partnerPair_of_mem M hM (Finset.mem_erase.mp he).2 hie)
    exact pairFactorB_update_of_notMem B hB v i w hie
  rw [hfirst, hrest]

/-- `prodB` is additive in each slot. -/
lemma prodB_update_add (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (v : Fin n → E)
    (i : Fin n) (x y : E) :
    prodB B hB M (Function.update v i (x + y)) =
      prodB B hB M (Function.update v i x) + prodB B hB M (Function.update v i y) := by
  rw [prodB_eq_mul_erase B hB M hM v i (x + y), prodB_eq_mul_erase B hB M hM v i x,
    prodB_eq_mul_erase B hB M hM v i y, B.map_add, LinearMap.add_apply]
  ring

/-- `prodB` is homogeneous in each slot. -/
lemma prodB_update_smul (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching M) (v : Fin n → E)
    (i : Fin n) (c : ℝ) (x : E) :
    prodB B hB M (Function.update v i (c • x)) = c * prodB B hB M (Function.update v i x) := by
  rw [prodB_eq_mul_erase B hB M hM v i (c • x), prodB_eq_mul_erase B hB M hM v i x, B.map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  ring

/-! ### The pairing sum as a multilinear map -/

/-- **P3b-i (i).** The pairing sum `Ψ(v) = Σ_{M ∈ matchings n} ∏_{e ∈ M} B(v_{e.1}, v_{e.2})`, as a
multilinear map. -/
def pairingML (n : ℕ) : MultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  MultilinearMap.mk (fun v => ∑ M ∈ matchings n, prodB B hB M v)
    (fun v i x y => by
      have h : (∑ M ∈ matchings n, prodB B hB M (Function.update v i (x + y)))
          = ∑ M ∈ matchings n, (prodB B hB M (Function.update v i x)
              + prodB B hB M (Function.update v i y)) :=
        Finset.sum_congr rfl fun M hM => prodB_update_add B hB M (mem_matchings.mp hM) v i x y
      rw [h, Finset.sum_add_distrib])
    (fun v i c x => by
      have h : (∑ M ∈ matchings n, prodB B hB M (Function.update v i (c • x)))
          = ∑ M ∈ matchings n, (c * prodB B hB M (Function.update v i x)) :=
        Finset.sum_congr rfl fun M hM => prodB_update_smul B hB M (mem_matchings.mp hM) v i c x
      rw [h, smul_eq_mul, Finset.mul_sum])

lemma pairingML_apply (v : Fin n → E) :
    pairingML B hB n v = ∑ M ∈ matchings n, prodB B hB M v :=
  rfl

/-- The image of `Sym2.mk` under the embedding induced by a permutation of the vertices. -/
lemma sym2Embedding_mk (σ : Equiv.Perm (Fin n)) (x y : Fin n) :
    (sym2Embedding σ.toEmbedding) (Sym2.mk x y) = Sym2.mk (σ x) (σ y) := by
  rw [show (sym2Embedding σ.toEmbedding) (Sym2.mk x y) =
    Sym2.map σ.toEmbedding (Sym2.mk x y) from rfl, Sym2.map_mk]
  rfl

/-- Relabelling the arguments relabels the pairs of each matching. -/
lemma prodB_map (M : Finset (Sym2 (Fin n))) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    prodB B hB M (v ∘ ⇑σ) = prodB B hB (M.map (sym2Embedding σ.toEmbedding)) v := by
  unfold prodB
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | h x y =>
    rw [pairFactorB_mk, Function.comp_apply, Function.comp_apply, sym2Embedding_mk,
      pairFactorB_mk]

/-- Relabelling the vertices by a permutation preserves the property of being a perfect
matching. -/
lemma isPerfectMatching_map (σ : Equiv.Perm (Fin n)) {M : Finset (Sym2 (Fin n))}
    (hM : IsPerfectMatching M) :
    IsPerfectMatching (M.map (sym2Embedding σ.toEmbedding)) := by
  refine ⟨?_, ?_⟩
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp he'
    exact not_isDiag_map σ.toEmbedding (hM.1 e he)
  · intro a
    obtain ⟨y, ⟨hyne, hymem⟩, hyuniq⟩ := hM.2 (σ.symm a)
    refine ⟨σ y, ⟨?_, ?_⟩, ?_⟩
    · intro h
      exact hyne (by rw [← h, Equiv.symm_apply_apply])
    · refine Finset.mem_map.mpr ⟨Sym2.mk (σ.symm a) y, hymem, ?_⟩
      rw [sym2Embedding_mk, Equiv.apply_symm_apply]
    · intro b hb
      obtain ⟨hbne, hbmem⟩ := hb
      obtain ⟨e, he, heq⟩ := Finset.mem_map.mp hbmem
      induction e using Sym2.ind with
      | h x y =>
        rw [sym2Embedding_mk, Sym2.eq_iff] at heq
        have hyx : σ.symm b ≠ σ.symm a := fun h => hbne (by simpa using congrArg σ h)
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hx : σ.symm a = x := by rw [← h1, Equiv.symm_apply_apply]
          have hy : σ.symm b = y := by rw [← h2, Equiv.symm_apply_apply]
          have hm' : Sym2.mk (σ.symm a) (σ.symm b) ∈ M := by rw [hx, hy]; exact he
          rw [← hyuniq (σ.symm b) ⟨hyx, hm'⟩, Equiv.apply_symm_apply]
        · have hx : σ.symm b = x := by rw [← h1, Equiv.symm_apply_apply]
          have hy : σ.symm a = y := by rw [← h2, Equiv.symm_apply_apply]
          have hm' : Sym2.mk (σ.symm a) (σ.symm b) ∈ M := by
            rw [hx, hy, sym2_mk_comm]; exact he
          rw [← hyuniq (σ.symm b) ⟨hyx, hm'⟩, Equiv.apply_symm_apply]

/-- Relabelling the pairs of a matching, as an embedding of finite sets of pairs. -/
def relabelMatching (σ : Equiv.Perm (Fin n)) :
    Finset (Sym2 (Fin n)) ↪ Finset (Sym2 (Fin n)) where
  toFun M := M.map (sym2Embedding σ.toEmbedding)
  inj' := by
    intro M₁ M₂ h
    have h' : M₁.map (sym2Embedding σ.toEmbedding) = M₂.map (sym2Embedding σ.toEmbedding) := h
    exact Finset.map_injective (sym2Embedding σ.toEmbedding) h'

/-- Relabelling the vertices by a permutation permutes the set of perfect matchings. -/
lemma matchings_map (σ : Equiv.Perm (Fin n)) :
    (matchings n).map (relabelMatching σ) = matchings n := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro M hM
    obtain ⟨M₀, hM₀, rfl⟩ := Finset.mem_map.mp hM
    exact mem_matchings.mpr (isPerfectMatching_map σ (mem_matchings.mp hM₀))
  · rw [Finset.card_map]

/-- **P3b-i (i), symmetry.** The pairing sum is invariant under relabelling the arguments. -/
theorem pairingML_isSymm (n : ℕ) : IsSymmMultilinear (pairingML B hB n) := by
  intro σ v
  rw [pairingML_apply, pairingML_apply]
  rw [Finset.sum_congr rfl (fun M _ => prodB_map B hB M v σ)]
  show (∑ M ∈ matchings n, prodB B hB (relabelMatching σ M) v) = ∑ M ∈ matchings n, prodB B hB M v
  rw [← Finset.sum_map (matchings n) (relabelMatching σ) (fun M => prodB B hB M v),
    matchings_map σ]

/-! ### The number of pairs of a perfect matching -/

/-- A perfect matching of `Fin n` consists of `n / 2` pairs. -/
lemma card_mul_two_of_isPerfectMatching {M : Finset (Sym2 (Fin n))} (hM : IsPerfectMatching M) :
    M.card * 2 = n := by
  have hmap : Set.MapsTo (fun a : Fin n => partnerPair M hM a)
      (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) (↑M : Set (Sym2 (Fin n))) :=
    fun a _ => partnerPair_mem M hM a
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hfiber : ∀ e ∈ M,
      ({a ∈ (Finset.univ : Finset (Fin n)) | partnerPair M hM a = e}).card = 2 := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have hxy : x ≠ y := fun h => hM.1 (Sym2.mk x y) he (by rw [Sym2.mk_isDiag_iff]; exact h)
      have hset : {a ∈ (Finset.univ : Finset (Fin n)) | partnerPair M hM a = Sym2.mk x y}
          = {x, y} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro ha
          have h2 : a ∈ Sym2.mk x y := by rw [← ha]; exact partnerPair_left M hM a
          rwa [Sym2.mem_iff] at h2
        · intro ha
          rcases ha with ha | ha
          · rw [ha, partnerPair, ← eq_partner M hM x hxy.symm he]
          · rw [ha, partnerPair, ← eq_partner M hM y hxy (by rw [sym2_mk_comm]; exact he)]
            exact sym2_mk_comm y x
      rw [hset, Finset.card_insert_of_notMem (by simpa using hxy)]
      simp
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, nsmul_eq_mul] at hcard
  exact hcard.symm

/-- **P3b-i (i), diagonal.** The diagonal value of the pairing sum. -/
lemma pairingML_const (v : E) :
    pairingML B hB n (fun _ : Fin n => v) = (B v v) ^ (n / 2) * (matchings n).card := by
  rw [pairingML_apply]
  have hterm : ∀ M ∈ matchings n, prodB B hB M (fun _ : Fin n => v) = (B v v) ^ (n / 2) := by
    intro M hM
    rw [prodB_const B hB]
    congr 1
    have h2 := card_mul_two_of_isPerfectMatching (mem_matchings.mp hM)
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ring

end Schwinger
