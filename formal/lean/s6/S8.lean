import S6Isserlis.S2

/-!
# S8 — P3b-i: the matching count `#(matchings (2k)) = (2k-1)!!`

Paper `cor:wick-hafnian` needs the number of pairings of `2k` labelled points, `(2k-1)!!`.
The frontier card records the route: the partner of the last vertex is unique, giving a
bijection `matchings (n+2) ≃ Σ q : Fin (n+1), matchings n`, hence the recurrence
`#(matchings (n+2)) = (n+1) * #(matchings n)`.

This module carries the relabelling infrastructure for that bijection: deleting the two
vertices `{last, q}` from `Fin (n+2)` leaves `Fin n`, realised concretely as the composite
`Fin.succAbove (Fin.last (n+1)) ∘ Fin.succAbove q₁` (with injectivity and the range
characterisation `mem_range_relabel_iff`), together with the inverse construction
`addPair` (relabel back and insert `{last, q}`) and the disjointness lemma
`newPair_not_mem`.  The remaining step (assembling the bijection, summing over the
`Fin (n+1)` fibres, and inducting) is recorded as outstanding in the frontier card.

Note (reconnaissance, 2026-09-17): the naive `decide`-based verification of the counts is
**not available** — `S2.lean` opens `Classical`, so kernel reduction of `(matchings n).card`
gets stuck at `Classical.choice`; `native_decide` is excluded by the project rule that the
axiom footprint stay `[propext, Classical.choice, Quot.sound]` (it would add
`Lean.trustCompiler`).  Hence the count must be obtained by the abstract recurrence below,
not by computation.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace Schwinger

variable {n : ℕ}

/-- The last vertex of `Fin (n+2)` is paired with a unique partner, which is not itself. -/
lemma partner_unique (M : Finset (Sym2 (Fin (n + 2)))) (hM : IsPerfectMatching M) :
    ∃! q : Fin (n + 2), q ≠ Fin.last (n + 1) ∧ Sym2.mk (Fin.last (n + 1)) q ∈ M := by
  unfold IsPerfectMatching at hM
  exact hM.2 (Fin.last (n + 1))

/-- Delete the pair `{last, q}`: after removing the last vertex and its partner `q₁`, the
remaining `n` vertices of `Fin (n+2)` are enumerated by the composite relabelling
`Fin n → Fin (n+1) → Fin (n+2)`. -/
def relabel (q₁ : Fin (n + 1)) : Fin n → Fin (n + 2) :=
  fun j => (Fin.last (n + 1)).succAbove (q₁.succAbove j)

/-- The relabelling is injective: it enumerates the complement of `{last, succAbove last q₁}`. -/
lemma relabel_injective (q₁ : Fin (n + 1)) : Function.Injective (relabel q₁) :=
  (Fin.succAbove_right_injective (p := Fin.last (n + 1))).comp
    (Fin.succAbove_right_injective (p := q₁))

/-- Membership characterisation of the relabelling: its range is exactly the complement of
the two deleted vertices. -/
lemma mem_range_relabel_iff (q₁ : Fin (n + 1)) (i : Fin (n + 2)) :
    i ∈ Set.range (relabel q₁) ↔ i ≠ Fin.last (n + 1) ∧ i ≠ (Fin.last (n + 1)).succAbove q₁ := by
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨Fin.succAbove_ne _ _, ?_⟩
    exact fun h => Fin.succAbove_ne q₁ j (Fin.succAbove_right_injective h)
  · rintro ⟨hL, hq⟩
    have hL' : i ∈ Set.range (Fin.succAbove (Fin.last (n + 1))) := by
      rw [Fin.range_succAbove]; exact hL
    obtain ⟨k, hk⟩ := hL'
    have hkq : k ≠ q₁ := by intro h; exact hq (by rw [← hk, h])
    have hk' : k ∈ Set.range (Fin.succAbove q₁) := by
      rw [Fin.range_succAbove]; exact hkq
    obtain ⟨j, hj⟩ := hk'
    exact ⟨j, by show (Fin.last (n + 1)).succAbove (q₁.succAbove j) = i; rw [hj, hk]⟩

/-! ### The inverse construction

Reversing the deletion: given a matching of `Fin n` and a slot `q₁`, add back the pair
`{last, succAbove last q₁}` and relabel the rest back.  `newPair_not_mem` is the disjointness
step that makes `addPair` an insertion into a set not already containing the pair. -/

/-- An injective map of the underlying type induces an embedding of unordered pairs. -/
def sym2Embedding {α β : Type*} (f : α ↪ β) : Sym2 α ↪ Sym2 β where
  toFun := Sym2.map f
  inj' := by
    intro a b h
    induction a using Sym2.ind with
    | h x y =>
      induction b using Sym2.ind with
      | h z w =>
        rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at h
        rw [Sym2.eq_iff]
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨f.injective h1, f.injective h2⟩
        · exact Or.inr ⟨f.injective h1, f.injective h2⟩

/-- `relabel` packaged as an embedding. -/
def relabelEmb (q₁ : Fin (n + 1)) : Fin n ↪ Fin (n + 2) := ⟨relabel q₁, relabel_injective q₁⟩

/-- The pair `{last, q}` added when reversing the deletion. -/
def newPair (q₁ : Fin (n + 1)) : Sym2 (Fin (n + 2)) :=
  Sym2.mk (Fin.last (n + 1)) ((Fin.last (n + 1)).succAbove q₁)

/-- Inverse of the deletion: add back the pair `{last, q}`. -/
def addPair (q₁ : Fin (n + 1)) (M : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin (n + 2))) :=
  insert (newPair q₁) (M.map (sym2Embedding (relabelEmb q₁)))

/-- The new pair is not among the relabelled pairs: it contains `last`, which the image avoids. -/
lemma newPair_not_mem (q₁ : Fin (n + 1)) (M : Finset (Sym2 (Fin n))) :
    newPair q₁ ∉ M.map (sym2Embedding (relabelEmb q₁)) := by
  intro hmem
  obtain ⟨e, -, he⟩ := Finset.mem_map.mp hmem
  have hL : Fin.last (n + 1) ∈ Sym2.map (relabel q₁) e := by
    rw [show Sym2.map (relabel q₁) e = newPair q₁ from he]
    exact (Sym2.mem_iff).mpr (Or.inl rfl)
  obtain ⟨a, -, ha⟩ := (Sym2.mem_map).mp hL
  exact Fin.succAbove_ne (Fin.last (n + 1)) (q₁.succAbove a) ha

/-- A non-degenerate pair stays non-degenerate under an injective relabelling. -/
lemma not_isDiag_map {α β : Type*} (f : α ↪ β) {e : Sym2 α} (he : ¬ e.IsDiag) :
    ¬ (Sym2.map f e).IsDiag := by
  induction e using Sym2.ind with
  | h x y =>
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
    exact fun h => he (by rw [Sym2.mk_isDiag_iff]; exact f.injective h)

/-- A vertex of a relabelled pair lies in the range of the relabelling. -/
lemma mem_range_of_mem_map {q₁ : Fin (n + 1)} {e : Sym2 (Fin n)} {a : Fin (n + 2)}
    (h : a ∈ Sym2.map (relabel q₁) e) : a ∈ Set.range (relabel q₁) := by
  obtain ⟨x, -, hx⟩ := (Sym2.mem_map).mp h
  exact ⟨x, hx⟩

/-- The last vertex is never produced by the relabelling. -/
lemma last_notMem_range (q₁ : Fin (n + 1)) : Fin.last (n + 1) ∉ Set.range (relabel q₁) := by
  intro h
  exact ((mem_range_relabel_iff q₁ (Fin.last (n + 1))).mp h).1 rfl

/-- Non-degeneracy is preserved by `addPair`: the first conjunct of `IsPerfectMatching`. -/
lemma addPair_nondeg (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin n))} (hM : IsPerfectMatching M) :
    ∀ e ∈ addPair q₁ M, ¬ e.IsDiag := by
  unfold IsPerfectMatching at hM
  intro e he
  rw [addPair, Finset.mem_insert] at he
  rcases he with rfl | he
  · show ¬ (Sym2.mk (Fin.last (n + 1)) ((Fin.last (n + 1)).succAbove q₁)).IsDiag
    rw [Sym2.mk_isDiag_iff]
    exact Ne.symm (Fin.succAbove_ne (Fin.last (n + 1)) q₁)
  · obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    exact not_isDiag_map (relabelEmb q₁) (hM.1 e' he')

/-! ### The unique-partner conjunct -/

/-- Unordered pairs commute. -/
lemma sym2_mk_comm {α : Type*} (a b : α) : Sym2.mk a b = Sym2.mk b a :=
  (Sym2.eq_iff).mpr (Or.inr ⟨rfl, rfl⟩)

/-- For a non-degenerate pair containing `a`, the pair has the form `{a, b}` with `b ≠ a`. -/
lemma exists_mk_of_mem {α : Type*} {e : Sym2 α} (hnd : ¬ e.IsDiag) {a : α} (ha : a ∈ e) :
    ∃ b, b ≠ a ∧ e = Sym2.mk a b := by
  induction e using Sym2.ind with
  | h u v =>
    rw [Sym2.mem_iff] at ha
    have huv : u ≠ v := fun h => hnd (by rw [h, Sym2.mk_isDiag_iff])
    rcases ha with h | h
    · subst h
      exact ⟨v, huv.symm, rfl⟩
    · subst h
      exact ⟨u, huv, sym2_mk_comm _ _⟩

/-- Every vertex of `Fin (n+2)` is either in the range of the relabelling, or is one of the
two deleted vertices `last` and `succAbove last q₁`. -/
lemma eq_last_or_eq_succAbove_of_notMem_range {q₁ : Fin (n + 1)} {a : Fin (n + 2)}
    (h : a ∉ Set.range (relabel q₁)) :
    a = Fin.last (n + 1) ∨ a = (Fin.last (n + 1)).succAbove q₁ := by
  by_cases hL : a = Fin.last (n + 1)
  · exact Or.inl hL
  · refine Or.inr ?_
    by_contra hq
    exact h ((mem_range_relabel_iff q₁ a).mpr ⟨hL, hq⟩)

/-- `succAbove last q₁` is not produced by the relabelling either. -/
lemma succAbove_notMem_range (q₁ : Fin (n + 1)) :
    (Fin.last (n + 1)).succAbove q₁ ∉ Set.range (relabel q₁) := by
  intro h
  exact ((mem_range_relabel_iff q₁ _).mp h).2 rfl

/-- If `M` is a perfect matching of `Fin (n+2)` that contains the special pair `{last, q}`, then
every vertex of every *other* pair lies in the range of the relabelling. -/
lemma vertices_mem_range (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin (n + 2)))}
    (hM : IsPerfectMatching M) (hp : newPair q₁ ∈ M) {e : Sym2 (Fin (n + 2))}
    (he : e ∈ M.erase (newPair q₁)) {a : Fin (n + 2)} (ha : a ∈ e) :
    a ∈ Set.range (relabel q₁) := by
  by_contra hcon
  unfold IsPerfectMatching at hM
  obtain ⟨hnd, huniq⟩ := hM
  have heM : e ∈ M := (Finset.mem_erase.mp he).2
  have hne : e ≠ newPair q₁ := (Finset.mem_erase.mp he).1
  rcases eq_last_or_eq_succAbove_of_notMem_range hcon with haL | haq
  · subst haL
    obtain ⟨b, hbne, hbe⟩ := exists_mk_of_mem (hnd e heM) ha
    obtain ⟨b', ⟨hb'ne, hb'mem⟩, hb'uniq⟩ := huniq (Fin.last (n + 1))
    have hqmem : Sym2.mk (Fin.last (n + 1)) ((Fin.last (n + 1)).succAbove q₁) ∈ M :=
      show newPair q₁ ∈ M from hp
    have hb1 : b = b' := hb'uniq b ⟨hbne, hbe ▸ heM⟩
    have hb2 : (Fin.last (n + 1)).succAbove q₁ = b' :=
      hb'uniq _ ⟨Fin.succAbove_ne _ _, hqmem⟩
    exact hne (by rw [hbe, hb1, ← hb2]; rfl)
  · subst haq
    obtain ⟨b, hbne, hbe⟩ := exists_mk_of_mem (hnd e heM) ha
    obtain ⟨b', ⟨hb'ne, hb'mem⟩, hb''uniq⟩ := huniq ((Fin.last (n + 1)).succAbove q₁)
    have hLmem : Sym2.mk ((Fin.last (n + 1)).succAbove q₁) (Fin.last (n + 1)) ∈ M := by
      rw [sym2_mk_comm]
      exact show newPair q₁ ∈ M from hp
    have hb1 : b = b' := hb''uniq b ⟨hbne, hbe ▸ heM⟩
    have hb2 : Fin.last (n + 1) = b' :=
      hb''uniq _ ⟨(Fin.succAbove_ne (Fin.last (n + 1)) q₁).symm, hLmem⟩
    exact hne (by
      rw [hbe, hb1, ← hb2, sym2_mk_comm ((Fin.last (n + 1)).succAbove q₁) (Fin.last (n + 1))]
      rfl)

/-- The unique partner of the last vertex in `addPair q₁ M` is `succAbove last q₁`. -/
lemma partner_at_last (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin n))} :
    ∃! b : Fin (n + 2),
      b ≠ Fin.last (n + 1) ∧ Sym2.mk (Fin.last (n + 1)) b ∈ addPair q₁ M := by
  refine ⟨(Fin.last (n + 1)).succAbove q₁, ⟨Fin.succAbove_ne _ _, ?_⟩, ?_⟩
  · rw [addPair, newPair]
    exact Finset.mem_insert.mpr (Or.inl rfl)
  · intro y hy
    obtain ⟨-, hymem⟩ := hy
    rw [addPair, Finset.mem_insert] at hymem
    rcases hymem with heq | himg
    · rw [newPair, Sym2.eq_iff] at heq
      rcases heq with ⟨-, hy'⟩ | ⟨hLq, -⟩
      · exact hy'
      · exact absurd hLq (Ne.symm (Fin.succAbove_ne (Fin.last (n + 1)) q₁))
    · obtain ⟨e', -, heq'⟩ := Finset.mem_map.mp himg
      have hL : Fin.last (n + 1) ∈ Sym2.map (relabel q₁) e' := by
        rw [show Sym2.map (relabel q₁) e' = Sym2.mk (Fin.last (n + 1)) y from heq']
        exact (Sym2.mem_iff).mpr (Or.inl rfl)
      exact absurd (mem_range_of_mem_map hL) (last_notMem_range q₁)

/-- The unique partner of `succAbove last q₁` in `addPair q₁ M` is the last vertex. -/
lemma partner_at_q (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin n))} :
    ∃! b : Fin (n + 2),
      b ≠ (Fin.last (n + 1)).succAbove q₁ ∧
        Sym2.mk ((Fin.last (n + 1)).succAbove q₁) b ∈ addPair q₁ M := by
  refine ⟨Fin.last (n + 1), ⟨(Fin.succAbove_ne (Fin.last (n + 1)) q₁).symm, ?_⟩, ?_⟩
  · have hcomm : Sym2.mk ((Fin.last (n + 1)).succAbove q₁) (Fin.last (n + 1)) = newPair q₁ := by
      rw [newPair, sym2_mk_comm]
    rw [addPair, hcomm]
    exact Finset.mem_insert.mpr (Or.inl rfl)
  · intro y hy
    obtain ⟨-, hymem⟩ := hy
    rw [addPair, Finset.mem_insert] at hymem
    rcases hymem with heq | himg
    · rw [newPair, Sym2.eq_iff] at heq
      rcases heq with ⟨hqL, -⟩ | ⟨-, hy'⟩
      · exact absurd hqL (Fin.succAbove_ne (Fin.last (n + 1)) q₁)
      · exact hy'
    · obtain ⟨e', -, heq'⟩ := Finset.mem_map.mp himg
      have hq : (Fin.last (n + 1)).succAbove q₁ ∈ Sym2.map (relabel q₁) e' := by
        rw [show Sym2.map (relabel q₁) e' =
          Sym2.mk ((Fin.last (n + 1)).succAbove q₁) y from heq']
        exact (Sym2.mem_iff).mpr (Or.inl rfl)
      exact absurd (mem_range_of_mem_map hq) (succAbove_notMem_range q₁)

/-- For a vertex in the range of the relabelling, the partner in `addPair q₁ M` is the
relabelled partner in `M`. -/
lemma partner_at_range (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin n))} (hM : IsPerfectMatching M)
    (a' : Fin n) :
    ∃! b : Fin (n + 2), b ≠ relabel q₁ a' ∧ Sym2.mk (relabel q₁ a') b ∈ addPair q₁ M := by
  unfold IsPerfectMatching at hM
  obtain ⟨b', ⟨hb'ne, hb'mem⟩, hb'uniq⟩ := hM.2 a'
  refine ⟨relabel q₁ b', ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact hb'ne (relabel_injective q₁ h)
  · rw [addPair, Finset.mem_insert]
    right
    exact Finset.mem_map.mpr ⟨Sym2.mk a' b', hb'mem, by
      show Sym2.map (relabel q₁) (Sym2.mk a' b') = Sym2.mk (relabel q₁ a') (relabel q₁ b')
      rw [Sym2.map_mk]⟩
  · intro y ⟨hyne, hymem⟩
    rw [addPair, Finset.mem_insert] at hymem
    rcases hymem with heq | himg
    · rw [newPair, Sym2.eq_iff] at heq
      have har : relabel q₁ a' ∈ Set.range (relabel q₁) := ⟨a', rfl⟩
      rcases heq with ⟨haL, -⟩ | ⟨haq, -⟩
      · exact absurd haL ((mem_range_relabel_iff q₁ _).mp har).1
      · exact absurd haq ((mem_range_relabel_iff q₁ _).mp har).2
    · obtain ⟨e'', he''mem, he''eq⟩ := Finset.mem_map.mp himg
      have hy : y ∈ Set.range (relabel q₁) := by
        have : y ∈ Sym2.map (relabel q₁) e'' := by
          rw [show Sym2.map (relabel q₁) e'' = Sym2.mk (relabel q₁ a') y from he''eq]
          exact (Sym2.mem_iff).mpr (Or.inr rfl)
        exact mem_range_of_mem_map this
      obtain ⟨y', hy'⟩ := hy
      have hy'ne : y' ≠ a' := fun h => hyne (by rw [← hy', h])
      have key : y' = b' := by
        apply hb'uniq
        refine ⟨hy'ne, ?_⟩
        induction e'' using Sym2.ind with
        | h u v =>
          change Sym2.map (relabel q₁) (Sym2.mk u v) = Sym2.mk (relabel q₁ a') y at he''eq
          rw [Sym2.map_mk, ← hy', Sym2.eq_iff] at he''eq
          rcases he''eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hu : u = a' := relabel_injective q₁ h1
            have hv : v = y' := relabel_injective q₁ h2
            rwa [hu, hv] at he''mem
          · have hu : u = y' := relabel_injective q₁ h1
            have hv : v = a' := relabel_injective q₁ h2
            rw [hu, hv, sym2_mk_comm] at he''mem
            exact he''mem
      rw [← hy', key]

/-- The unique-partner (second) conjunct of `IsPerfectMatching` is preserved by `addPair`. -/
lemma addPair_partner (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin n))} (hM : IsPerfectMatching M) :
    ∀ a : Fin (n + 2), ∃! b : Fin (n + 2), b ≠ a ∧ Sym2.mk a b ∈ addPair q₁ M := by
  intro a
  by_cases ha : a ∈ Set.range (relabel q₁)
  · obtain ⟨a', rfl⟩ := ha
    exact partner_at_range q₁ hM a'
  · rcases eq_last_or_eq_succAbove_of_notMem_range ha with h | h
    · subst h; exact partner_at_last q₁
    · subst h; exact partner_at_q q₁

/-- `addPair q₁` maps perfect matchings of `Fin n` to perfect matchings of `Fin (n+2)`. -/
lemma addPair_isPerfectMatching (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin n))}
    (hM : IsPerfectMatching M) : IsPerfectMatching (addPair q₁ M) :=
  ⟨addPair_nondeg q₁ hM, addPair_partner q₁ hM⟩

/-- `addPair q₁` is injective.  (No matching hypothesis is needed: the proof only uses that
the added pair is never produced by the relabelling.) -/
lemma addPair_injective (q₁ : Fin (n + 1)) : Function.Injective (addPair q₁) := by
  intro M M' h
  have h1 : newPair q₁ ∉ M.map (sym2Embedding (relabelEmb q₁)) := newPair_not_mem q₁ M
  have h2 : newPair q₁ ∉ M'.map (sym2Embedding (relabelEmb q₁)) := newPair_not_mem q₁ M'
  have hmap : M.map (sym2Embedding (relabelEmb q₁))
      = M'.map (sym2Embedding (relabelEmb q₁)) := by
    have hc := congrArg (fun s => s.erase (newPair q₁)) h
    rw [addPair, addPair, Finset.erase_insert h1, Finset.erase_insert h2] at hc
    exact hc
  exact (Finset.map_inj).mp hmap

/-- The image of `matchings n` under `addPair q₁` has the same cardinality. -/
lemma card_image_addPair (q₁ : Fin (n + 1)) :
    ((matchings n).map ⟨addPair q₁, addPair_injective q₁⟩).card = (matchings n).card :=
  Finset.card_map _

/-! ### The inverse direction

The inverse of `addPair q₁` needs a total vertex map `Fin (n+2) → Fin n`, which cannot exist
when `Fin n` is empty.  Hence the standing hypothesis `Nonempty (Fin n)` (i.e. `n ≥ 1`); the
`n = 0` case of the recurrence is a separate base case. -/

section Inv

variable [Nonempty (Fin n)]

/-- Inverse of the relabelling (correct on the range; arbitrary off it). -/
def relabelInv (q₁ : Fin (n + 1)) : Fin (n + 2) → Fin n := Function.invFun (relabel q₁)

/-- On the range, `relabelInv` inverts `relabel`. -/
lemma relabelInv_relabel (q₁ : Fin (n + 1)) (a : Fin n) : relabelInv q₁ (relabel q₁ a) = a :=
  Function.leftInverse_invFun (relabel_injective q₁) a

/-- Pulling a relabelled pair back recovers the pair. -/
lemma sym2_inv_map (q₁ : Fin (n + 1)) (e : Sym2 (Fin n)) :
    Sym2.map (relabelInv q₁) (Sym2.map (relabel q₁) e) = e := by
  rw [Sym2.map_map]
  have hcomp : (relabelInv q₁) ∘ (relabel q₁) = id := funext (relabelInv_relabel q₁)
  rw [hcomp, Sym2.map_id]
  rfl

/-- On the range of the relabelling, `relabelInv` undoes `relabel`. -/
lemma relabel_relabelInv (q₁ : Fin (n + 1)) {a : Fin (n + 2)}
    (ha : a ∈ Set.range (relabel q₁)) : relabel q₁ (relabelInv q₁ a) = a := by
  obtain ⟨x, rfl⟩ := ha
  rw [relabelInv_relabel]

/-- `relabelInv` is injective on the range of the relabelling. -/
lemma relabelInv_injOn (q₁ : Fin (n + 1)) :
    Set.InjOn (relabelInv q₁) (Set.range (relabel q₁)) := by
  intro a ha b hb h
  rw [← relabel_relabelInv q₁ ha, ← relabel_relabelInv q₁ hb, h]

/-- A pair all of whose vertices lie in the range of the relabelling stays non-degenerate
after pulling back by `relabelInv`. -/
lemma not_isDiag_inv_map (q₁ : Fin (n + 1)) {e : Sym2 (Fin (n + 2))} (hnd : ¬ e.IsDiag)
    (hall : ∀ a ∈ e, a ∈ Set.range (relabel q₁)) :
    ¬ (Sym2.map (relabelInv q₁) e).IsDiag := by
  induction e using Sym2.ind with
  | h x y =>
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff] at *
    intro h
    exact hnd (relabelInv_injOn q₁
      (hall x (Sym2.mem_iff.mpr (Or.inl rfl)))
      (hall y (Sym2.mem_iff.mpr (Or.inr rfl))) h)

/-- Pulling back along the relabelling and pushing forward again is the identity, for a pair
whose vertices all lie in the range of the relabelling. -/
lemma map_relabel_map_relabelInv (q₁ : Fin (n + 1)) {e : Sym2 (Fin (n + 2))}
    (hall : ∀ a ∈ e, a ∈ Set.range (relabel q₁)) :
    Sym2.map (relabel q₁) (Sym2.map (relabelInv q₁) e) = e := by
  rw [Sym2.map_map]
  have h : Sym2.map (relabel q₁ ∘ relabelInv q₁) e = Sym2.map id e :=
    Sym2.map_congr (fun a ha => relabel_relabelInv q₁ (hall a ha))
  rw [h, Sym2.map_id]
  rfl

/-- Remove the special pair and relabel back: the candidate inverse of `addPair`. -/
def strip (q₁ : Fin (n + 1)) (M : Finset (Sym2 (Fin (n + 2)))) : Finset (Sym2 (Fin n)) :=
  (M.erase (newPair q₁)).image (Sym2.map (relabelInv q₁))

/-- The round trip `strip ∘ addPair` is the identity. -/
lemma strip_addPair (q₁ : Fin (n + 1)) (M : Finset (Sym2 (Fin n))) :
    strip q₁ (addPair q₁ M) = M := by
  have hnot : newPair q₁ ∉ M.map (sym2Embedding (relabelEmb q₁)) := newPair_not_mem q₁ M
  unfold strip addPair
  rw [Finset.erase_insert hnot, Finset.map_eq_image, Finset.image_image]
  have hcomp : Sym2.map (relabelInv q₁) ∘ ⇑(sym2Embedding (relabelEmb q₁)) = id := by
    funext e
    exact sym2_inv_map q₁ e
  rw [hcomp, Finset.image_id]

/-- Non-degeneracy of `strip`, i.e. the first conjunct of `IsPerfectMatching`. -/
lemma strip_nondeg (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin (n + 2)))}
    (hM : IsPerfectMatching M) (hp : newPair q₁ ∈ M) :
    ∀ e ∈ strip q₁ M, ¬ e.IsDiag := by
  unfold IsPerfectMatching at hM
  intro e he
  unfold strip at he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  exact not_isDiag_inv_map q₁ (hM.1 f (Finset.mem_erase.mp hf).2)
    (fun a ha => vertices_mem_range q₁ ⟨hM.1, hM.2⟩ hp hf ha)

/-- The unique-partner (second) conjunct of `IsPerfectMatching` for `strip`. -/
lemma strip_partner (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin (n + 2)))}
    (hM : IsPerfectMatching M) (hp : newPair q₁ ∈ M) :
    ∀ a' : Fin n, ∃! b' : Fin n, b' ≠ a' ∧ Sym2.mk a' b' ∈ strip q₁ M := by
  unfold IsPerfectMatching at hM
  obtain ⟨hnd, huniq⟩ := hM
  intro a'
  obtain ⟨b, ⟨hbne, hbmem⟩, hbuniq⟩ := huniq (relabel q₁ a')
  have har : relabel q₁ a' ∈ Set.range (relabel q₁) := ⟨a', rfl⟩
  have hmne : Sym2.mk (relabel q₁ a') b ≠ newPair q₁ := by
    intro h
    rw [newPair, Sym2.eq_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ((mem_range_relabel_iff q₁ _).mp har).1 h1
    · exact ((mem_range_relabel_iff q₁ _).mp har).2 h1
  have hmem' : Sym2.mk (relabel q₁ a') b ∈ M.erase (newPair q₁) :=
    Finset.mem_erase.mpr ⟨hmne, hbmem⟩
  have hbr : b ∈ Set.range (relabel q₁) :=
    vertices_mem_range q₁ ⟨hnd, huniq⟩ hp hmem' (Sym2.mem_iff.mpr (Or.inr rfl))
  obtain ⟨b', hb'⟩ := hbr
  refine ⟨b', ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact hbne (by rw [← hb', h])
  · unfold strip
    refine Finset.mem_image.mpr ⟨Sym2.mk (relabel q₁ a') b, hmem', ?_⟩
    rw [Sym2.map_mk, relabelInv_relabel q₁ a', ← hb', relabelInv_relabel q₁ b']
  · intro y ⟨hyne, hymem⟩
    unfold strip at hymem
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hymem
    have heall : ∀ a ∈ e, a ∈ Set.range (relabel q₁) :=
      fun a ha => vertices_mem_range q₁ ⟨hnd, huniq⟩ hp he ha
    have he' : e = Sym2.mk (relabel q₁ a') (relabel q₁ y) := by
      have h1 := congrArg (Sym2.map (relabel q₁)) heq
      rw [map_relabel_map_relabelInv q₁ heall, Sym2.map_mk] at h1
      exact h1
    have hpart : relabel q₁ y = b := by
      refine hbuniq (relabel q₁ y) ⟨fun h => hyne (relabel_injective q₁ h), ?_⟩
      rw [← he']
      exact (Finset.mem_erase.mp he).2
    exact relabel_injective q₁ (by rw [hpart, ← hb'])

/-- `strip q₁` maps perfect matchings of `Fin (n+2)` containing the special pair to perfect
matchings of `Fin n`. -/
lemma strip_isPerfectMatching (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin (n + 2)))}
    (hM : IsPerfectMatching M) (hp : newPair q₁ ∈ M) :
    IsPerfectMatching (strip q₁ M) :=
  ⟨strip_nondeg q₁ hM hp, strip_partner q₁ hM hp⟩

/-- The reverse round trip: if `M` contains the special pair, `addPair` undoes `strip`. -/
lemma addPair_strip (q₁ : Fin (n + 1)) {M : Finset (Sym2 (Fin (n + 2)))}
    (hM : IsPerfectMatching M) (hp : newPair q₁ ∈ M) : addPair q₁ (strip q₁ M) = M := by
  have hmap : (strip q₁ M).map (sym2Embedding (relabelEmb q₁)) = M.erase (newPair q₁) := by
    have hpt : ∀ e ∈ M.erase (newPair q₁),
        Sym2.map (relabel q₁) (Sym2.map (relabelInv q₁) e) = e :=
      fun e he => map_relabel_map_relabelInv q₁ (fun a ha => vertices_mem_range q₁ hM hp he ha)
    unfold strip
    rw [Finset.map_eq_image, Finset.image_image]
    have himg : Finset.image
        (⇑(sym2Embedding (relabelEmb q₁)) ∘ Sym2.map (relabelInv q₁)) (M.erase (newPair q₁))
        = Finset.image id (M.erase (newPair q₁)) :=
      Finset.image_congr (fun x hx => hpt x hx)
    rw [himg, Finset.image_id]
  unfold addPair
  rw [hmap]
  exact Finset.insert_erase hp

end Inv

/-! ### Counting: the recurrence `#(matchings (n+2)) = (n+1) * #(matchings n)`

Partition `matchings (n+2)` into the fibres over the slot `q₁` of the special pair.  By
`fiber_eq_map` each fibre is the image of `matchings n` under `addPair q₁`, hence has the same
cardinality; the fibres are disjoint (`fiber_disjoint`) and cover everything
(`biUnion_fiber`).  -/

/-- Membership in `matchings`. -/
@[simp] lemma mem_matchings {n : ℕ} {M : Finset (Sym2 (Fin n))} :
    M ∈ matchings n ↔ IsPerfectMatching M := by
  unfold matchings
  simp

/-- The special pairs for distinct slots are distinct. -/
lemma newPair_injective : Function.Injective (newPair (n := n)) := by
  intro q₁ q₂ h
  unfold newPair at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact Fin.succAbove_right_injective h2
  · exact absurd h1 (Ne.symm (Fin.succAbove_ne (Fin.last (n + 1)) q₂))

/-- The matchings of `Fin (n+2)` whose special pair uses slot `q₁`. -/
def fiber (q₁ : Fin (n + 1)) : Finset (Finset (Sym2 (Fin (n + 2)))) :=
  (matchings (n + 2)).filter (fun M => newPair q₁ ∈ M)

/-- The special pair is determined by the matching: a perfect matching contains at most one. -/
lemma newPair_eq_of_mem {M : Finset (Sym2 (Fin (n + 2)))} (hM : IsPerfectMatching M)
    {q₁ q₂ : Fin (n + 1)} (h1 : newPair q₁ ∈ M) (h2 : newPair q₂ ∈ M) : q₁ = q₂ := by
  unfold IsPerfectMatching at hM
  obtain ⟨b, ⟨hbne, hbmem⟩, hbuniq⟩ := hM.2 (Fin.last (n + 1))
  have e1 : (Fin.last (n + 1)).succAbove q₁ = b :=
    hbuniq _ ⟨Fin.succAbove_ne _ _, show newPair q₁ ∈ M from h1⟩
  have e2 : (Fin.last (n + 1)).succAbove q₂ = b :=
    hbuniq _ ⟨Fin.succAbove_ne _ _, show newPair q₂ ∈ M from h2⟩
  exact Fin.succAbove_right_injective (by rw [e1, e2])

/-- Distinct fibres are disjoint. -/
lemma fiber_disjoint {q₁ q₂ : Fin (n + 1)} (h : q₁ ≠ q₂) : Disjoint (fiber q₁) (fiber q₂) := by
  rw [Finset.disjoint_left]
  intro M h1 h2
  rw [fiber, Finset.mem_filter] at h1 h2
  exact h (newPair_eq_of_mem ((mem_matchings).mp h1.1) h1.2 h2.2)

/-- Every perfect matching uses exactly one slot, so the fibres cover `matchings (n+2)`. -/
lemma biUnion_fiber : (Finset.univ : Finset (Fin (n + 1))).biUnion fiber = matchings (n + 2) := by
  ext M
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨q, -, hq⟩
    rw [fiber, Finset.mem_filter] at hq
    exact hq.1
  · intro hM
    have hPM : IsPerfectMatching M := (mem_matchings).mp hM
    unfold IsPerfectMatching at hPM
    obtain ⟨b, ⟨hbne, hbmem⟩, -⟩ := hPM.2 (Fin.last (n + 1))
    have hbr : b ∈ Set.range (Fin.succAbove (Fin.last (n + 1))) := by
      rw [Fin.range_succAbove]; exact hbne
    obtain ⟨q, hq⟩ := hbr
    refine ⟨q, Finset.mem_univ _, ?_⟩
    rw [fiber, Finset.mem_filter]
    refine ⟨hM, ?_⟩
    show Sym2.mk (Fin.last (n + 1)) ((Fin.last (n + 1)).succAbove q) ∈ M
    rw [hq]
    exact hbmem

section Inv

variable [Nonempty (Fin n)]

/-- `addPair q₁` bijects `matchings n` onto the fibre over `q₁`. -/
lemma fiber_eq_map (q₁ : Fin (n + 1)) :
    fiber q₁ = (matchings n).map ⟨addPair q₁, addPair_injective q₁⟩ := by
  ext M
  rw [fiber, Finset.mem_filter, mem_matchings, Finset.mem_map]
  constructor
  · rintro ⟨hM, hp⟩
    exact ⟨strip q₁ M, (mem_matchings).mpr (strip_isPerfectMatching q₁ hM hp),
      addPair_strip q₁ hM hp⟩
  · rintro ⟨N, hN, rfl⟩
    exact ⟨addPair_isPerfectMatching q₁ ((mem_matchings).mp hN), Finset.mem_insert_self _ _⟩

/-- Every fibre has the cardinality of `matchings n`. -/
lemma fiber_card (q₁ : Fin (n + 1)) : (fiber q₁).card = (matchings n).card := by
  rw [fiber_eq_map, Finset.card_map]

/-- **The recurrence**: `#(matchings (n+2)) = (n+1) * #(matchings n)`, for `n ≥ 1`. -/
theorem card_matchings_add_two :
    (matchings (n + 2)).card = (n + 1) * (matchings n).card := by
  rw [← biUnion_fiber, Finset.card_biUnion (fun a _ b _ h => fiber_disjoint h),
    Finset.sum_congr rfl (fun q _ => fiber_card q)]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Inv

/-! ### The base cases and the closed form `#(matchings (2k)) = (2k-1)‼`

The recurrence needs `Nonempty (Fin n)`, so `n = 0` is not covered and the two small cases
`#(matchings 0) = 1` and `#(matchings 2) = 1` are proved by hand (they cannot be obtained by
`decide`, since `matchings` is defined under `Classical`). -/

/-- Every element of `Fin 2` is `0` or `1`. -/
lemma fin_two_eq (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- There is exactly one perfect matching of `Fin 0`, namely the empty set. -/
lemma matchings_zero : matchings 0 = {∅} := by
  ext M
  rw [Finset.mem_singleton, mem_matchings]
  constructor
  · intro _
    ext e
    constructor
    · intro _
      induction e using Sym2.ind with
      | h a b => exact Fin.elim0 a
    · intro he
      exact absurd he (Finset.notMem_empty e)
  · intro hM
    rw [hM]
    exact ⟨fun e he => absurd he (Finset.notMem_empty e), fun a => Fin.elim0 a⟩

lemma card_matchings_zero : (matchings 0).card = 1 := by
  rw [matchings_zero, Finset.card_singleton]

/-- The unique perfect matching of `Fin 2` is `{s(0,1)}`. -/
lemma matchings_two :
    matchings 2 = {({Sym2.mk (0 : Fin 2) 1} : Finset (Sym2 (Fin 2)))} := by
  ext M
  rw [Finset.mem_singleton, mem_matchings]
  constructor
  · intro hM
    unfold IsPerfectMatching at hM
    obtain ⟨hnd, huniq⟩ := hM
    obtain ⟨b, ⟨hbne, hbmem⟩, -⟩ := huniq 0
    have hb : b = 1 := by
      rcases fin_two_eq b with h | h
      · exact absurd h hbne
      · exact h
    rw [hb] at hbmem
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hbmem, ?_⟩
    intro x hx
    induction x using Sym2.ind with
    | h u v =>
      have hnd' : u ≠ v := by
        have := hnd _ hx
        rwa [Sym2.mk_isDiag_iff] at this
      rcases fin_two_eq u with hu | hu <;> rcases fin_two_eq v with hv | hv
      · exact absurd (hu.trans hv.symm) hnd'
      · rw [hu, hv]
      · rw [hu, hv, sym2_mk_comm]
      · exact absurd (hu.trans hv.symm) hnd'
  · intro hM
    rw [hM]
    refine ⟨?_, ?_⟩
    · intro e he
      rw [Finset.mem_singleton] at he
      rw [he, Sym2.mk_isDiag_iff]
      decide
    · intro a
      rcases fin_two_eq a with ha | ha
      · subst ha
        refine ⟨1, ⟨by decide, by rw [Finset.mem_singleton]⟩, ?_⟩
        intro y hy
        obtain ⟨hyne, hymem⟩ := hy
        rw [Finset.mem_singleton, Sym2.eq_iff] at hymem
        rcases hymem with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact h2
        · exact absurd h1 (by decide : ¬ ((0 : Fin 2) = 1))
      · subst ha
        refine ⟨0, ⟨by decide, ?_⟩, ?_⟩
        · rw [Finset.mem_singleton, sym2_mk_comm]
        · intro y hy
          obtain ⟨hyne, hymem⟩ := hy
          rw [Finset.mem_singleton, Sym2.eq_iff] at hymem
          rcases hymem with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact absurd h1 (by decide : ¬ ((1 : Fin 2) = 0))
          · exact h2

lemma card_matchings_two : (matchings 2).card = 1 := by
  rw [matchings_two, Finset.card_singleton]

/-- **The matching count**: `#(matchings (2k)) = (2k-1)‼`, i.e. paper `cor:wick-hafnian`'s
combinatorial input. -/
theorem card_matchings_two_mul (k : ℕ) :
    (matchings (2 * k)).card = Nat.doubleFactorial (2 * k - 1) := by
  induction k with
  | zero => rw [Nat.mul_zero, card_matchings_zero]; rfl
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [show 2 * (0 + 1) = 2 by norm_num, card_matchings_two]
      rfl
    · haveI : Nonempty (Fin (2 * k)) := ⟨⟨0, by omega⟩⟩
      have hrec := card_matchings_add_two (n := 2 * k)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, hrec, ih,
        show 2 * k + 2 - 1 = 2 * k + 1 by omega, Nat.doubleFactorial_add_one]

end Schwinger
