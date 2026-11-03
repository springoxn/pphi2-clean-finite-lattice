/-
Ursell/Mayer 组合核的**第四块** —— 引理 3.1 一般形式（`S = A ⊔ B` 横向相容、
`B` 内部**可以**有边 ⇒ `φ(S) = 0`）所需的**子集双和分解**。

**口径**：见 `UrsellCore.lean` 文件头（`proofs/pphi2_cluster_expansion.md` 的 `(2.2)`；
相容集 = 不可相容图 `I` 的独立集）。证明骨架见 `pphi2_formalization_plan.md` §4.8.1。

**本文件证了什么**

1. `sum_powerset_insert`：`(insert b B).powerset` 上的和 = `B.powerset` 上的和 + `B.powerset` 上
   `insert b` 之后的和（`Finset.powerset_insert` + `sum_union` + `sum_image`）。
2. `sum_powerset_union`：**双和分解** —— `A`、`B` 不交时
   `∑_{T ⊆ A ∪ B} f T = ∑_{X ⊆ A} ∑_{Y ⊆ B} f (X ∪ Y)`（对 `B` 归纳）。

**明确不在本文件内**：一般形式的 `ursell` 定理本身；`(2.1)` 指数公式路线；
引理 3.1 的另一半；定理 3.2 / 3.3。
-/
import S6Isserlis.UrsellSplit
import Mathlib.Tactic

noncomputable section

open scoped Classical
open Finset

namespace Pphi2Ursell

variable {V : Type*} [LinearOrder V]

/-! ### §6 子集双和分解 -/

/-- `insert b` 在"不含 `b` 的集合族"上单射。 -/
private theorem insert_injOn_powerset {B : Finset V} {b : V} (hb : b ∉ B) :
    Set.InjOn (fun T : Finset V => insert b T) ↑B.powerset := by
  intro T hT T' hT' hEq
  have hbT : b ∉ T := fun h => hb (Finset.mem_powerset.mp hT h)
  have hbT' : b ∉ T' := fun h => hb (Finset.mem_powerset.mp hT' h)
  have h := congrArg (fun s : Finset V => s.erase b) hEq
  simpa [Finset.erase_insert hbT, Finset.erase_insert hbT'] using h

/-- `(insert b B).powerset` 上的和 = `B.powerset` 上的和 + `B.powerset` 上"先 `insert b`"的和。 -/
private theorem sum_powerset_insert {M : Type*} [AddCommMonoid M] (f : Finset V → M)
    {B : Finset V} {b : V} (hb : b ∉ B) :
    ∑ T ∈ (insert b B).powerset, f T
      = (∑ T ∈ B.powerset, f T) + ∑ T ∈ B.powerset, f (insert b T) := by
  rw [Finset.powerset_insert]
  have hdisj : Disjoint B.powerset (B.powerset.image (fun T => insert b T)) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨T₀, hT₀, hEq⟩ := Finset.mem_image.mp hT'
    rw [← hEq] at hT
    exact (fun h => hb (Finset.mem_powerset.mp hT h)) (Finset.mem_insert_self b T₀)
  rw [Finset.sum_union hdisj, Finset.sum_image (insert_injOn_powerset hb)]

/-- **双和分解**：`A`、`B` 不交时，`A ∪ B` 的所有子集上的和 = 按 `(X ⊆ A, Y ⊆ B)` 的双和。 -/
theorem sum_powerset_union {M : Type*} [AddCommMonoid M] :
    ∀ B : Finset V, ∀ (f : Finset V → M) (A : Finset V), Disjoint A B →
      ∑ T ∈ (A ∪ B).powerset, f T = ∑ X ∈ A.powerset, ∑ Y ∈ B.powerset, f (X ∪ Y) := by
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro f A _
    simp [Finset.union_empty]
  | insert b B' hb ih =>
    intro f A hAB
    have hbA : b ∉ A := fun h => Finset.disjoint_left.mp hAB h (Finset.mem_insert_self b B')
    have hbAB' : b ∉ A ∪ B' := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact hbA h
      · exact hb h
    have hAB' : Disjoint A B' := hAB.mono (Finset.Subset.refl A) (Finset.subset_insert b B')
    have hunion : A ∪ insert b B' = insert b (A ∪ B') := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hunion, sum_powerset_insert f hbAB', ih f A hAB', ih (fun T => f (insert b T)) A hAB']
    have hinner : ∀ X : Finset V,
        ∑ Y ∈ (insert b B').powerset, f (X ∪ Y)
          = (∑ Y ∈ B'.powerset, f (X ∪ Y)) + ∑ Y ∈ B'.powerset, f (insert b (X ∪ Y)) := by
      intro X
      have h2 : (∑ Y ∈ B'.powerset, f (X ∪ insert b Y))
          = ∑ Y ∈ B'.powerset, f (insert b (X ∪ Y)) :=
        Finset.sum_congr rfl (fun Y _ => by
          rw [show X ∪ insert b Y = insert b (X ∪ Y) from by
            ext x
            simp only [Finset.mem_union, Finset.mem_insert]
            tauto])
      rw [sum_powerset_insert (fun Y => f (X ∪ Y)) hb, h2]
    rw [Finset.sum_congr rfl (fun X _ => hinner X), Finset.sum_add_distrib]

/-! ### §7 差集的并分解（一般形式装配的第 3a 步） -/

/-- `(A ∪ B) ∖ (X ∪ Y) = (A ∖ X) ∪ (B ∖ Y)`（`X ⊆ A`、`Y ⊆ B`、`A`、`B` 不交）。 -/
theorem sdiff_union_sdiff {A B X Y : Finset V} (hXA : X ⊆ A) (hYB : Y ⊆ B)
    (hAB : Disjoint A B) : (A ∪ B) \ (X ∪ Y) = (A \ X) ∪ (B \ Y) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hxXY⟩
    · exact Or.inl ⟨hx, fun h => hxXY (Or.inl h)⟩
    · exact Or.inr ⟨hx, fun h => hxXY (Or.inr h)⟩
  · rintro (⟨hxA, hxX⟩ | ⟨hxB, hxY⟩)
    · refine ⟨Or.inl hxA, ?_⟩
      rintro (h | h)
      · exact hxX h
      · exact Finset.disjoint_left.mp hAB hxA (hYB h)
    · refine ⟨Or.inr hxB, ?_⟩
      rintro (h | h)
      · exact Finset.disjoint_left.mp hAB (hXA h) hxB
      · exact hxY h

/-- 相容性指示子在**差集的并**上可乘：`[(A∪B)∖(X∪Y) 相容] = [A∖X 相容]·[B∖Y 相容]`。 -/
theorem compatInd_sdiff_union_sdiff {I : SimpleGraph V} {A B X Y : Finset V}
    (hXA : X ⊆ A) (hYB : Y ⊆ B) (hAB : Disjoint A B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ I.Adj a b) :
    compatInd I ((A ∪ B) \ (X ∪ Y)) = compatInd I (A \ X) * compatInd I (B \ Y) := by
  rw [sdiff_union_sdiff hXA hYB hAB,
    compatInd_union (A := A \ X) (B := B \ Y) (fun a ha b hb =>
      hcross a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)]

/-! ### §8 一般形式：`S = A ⊔ B` 横向相容 ⇒ `φ(S) = 0`（引理 3.1 的"不连通 ⇒ 0"方向） -/

/-- 辅助（对 `S` 强归纳）：假定 `S` 的最小元落在 `A` 一侧。 -/
private theorem ursell_split_aux (I : SimpleGraph V) :
    ∀ S : Finset V, ∀ A B : Finset V, S = A ∪ B → Disjoint A B → A.Nonempty → B.Nonempty →
      (∀ a ∈ A, ∀ b ∈ B, ¬ I.Adj a b) → (hSne : S.Nonempty) → S.min' hSne ∈ A →
      ursell I S = 0 := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro A B hS hAB hAne hBne hcross hSne hminA
    subst hS
    set m := (A ∪ B).min' hSne with hmdef
    have hmA : m ∈ A := hminA
    have hmle : ∀ x ∈ A ∪ B, m ≤ x := by
      intro x hx
      rw [hmdef]
      exact Finset.min'_le (A ∪ B) x hx
    have hminT : ∀ {T : Finset V}, T ⊆ A ∪ B → m ∈ T → ∀ hT : T.Nonempty, T.min' hT = m := by
      intro T hTsub hmT hT
      exact le_antisymm (Finset.min'_le T m hmT)
        (Finset.le_min' T hT m (fun y hy => hmle y (hTsub hy)))
    -- 归纳假设：`X ⊆ A`、`Y ⊆ B`、`X ∋ m`、`Y ≠ ∅`、`X ∪ Y ⊊ S` ⇒ `φ(X ∪ Y) = 0`
    have hvanish : ∀ {X Y : Finset V}, X ⊆ A → Y ⊆ B → m ∈ X → Y.Nonempty →
        X ∪ Y ⊂ A ∪ B → ursell I (X ∪ Y) = 0 := by
      intro X Y hXA hYB hmX hYne hlt
      have hXne : X.Nonempty := ⟨m, hmX⟩
      have hXYne : (X ∪ Y).Nonempty := hXne.mono Finset.subset_union_left
      have hminX : (X ∪ Y).min' hXYne ∈ X := by
        rw [hminT (Finset.union_subset_union hXA hYB) (Finset.mem_union_left Y hmX) hXYne]
        exact hmX
      exact ih (X ∪ Y) hlt X Y rfl (hAB.mono hXA hYB) hXne hYne
        (fun a ha b hb => hcross a (hXA ha) b (hYB hb)) hXYne hminX
    -- (1)(2) 续接方程 + 双和分解
    have hFULL : (∑ T ∈ (A ∪ B).powerset.filter (fun T => m ∈ T),
        ursell I T * compatInd I ((A ∪ B) \ T)) = compatInd I (A ∪ B) :=
      (compatInd_eq_sum I hSne).symm
    have hdecomp : (∑ T ∈ (A ∪ B).powerset.filter (fun T => m ∈ T),
        ursell I T * compatInd I ((A ∪ B) \ T))
        = ∑ X ∈ A.powerset.filter (fun X => m ∈ X), ∑ Y ∈ B.powerset,
            ursell I (X ∪ Y) * compatInd I ((A ∪ B) \ (X ∪ Y)) := by
      rw [Finset.sum_filter, Finset.sum_filter,
        sum_powerset_union B
          (fun T => if m ∈ T then ursell I T * compatInd I ((A ∪ B) \ T) else 0) A hAB]
      refine Finset.sum_congr rfl ?_
      intro X hX
      by_cases hmX : m ∈ X
      · rw [ite_eq_left hmX]
        refine Finset.sum_congr rfl (fun Y _ => ?_)
        rw [ite_eq_left (show m ∈ X ∪ Y from Finset.mem_union_left Y hmX)]
      · rw [ite_eq_right hmX]
        refine Finset.sum_eq_zero (fun Y hY => ?_)
        have hnot : ¬ (m ∈ X ∪ Y) := by
          rw [Finset.mem_union]
          rintro (h | h)
          · exact hmX h
          · exact Finset.disjoint_left.mp hAB hmA (Finset.mem_powerset.mp hY h)
        rw [ite_eq_right hnot]
    -- (3) 内层求和
    have hinner : ∀ X ∈ A.powerset.filter (fun X => m ∈ X),
        (∑ Y ∈ B.powerset, ursell I (X ∪ Y) * compatInd I ((A ∪ B) \ (X ∪ Y)))
          = compatInd I (A \ X) * (ursell I X * compatInd I B)
            + (if X = A then ursell I (A ∪ B) else 0) := by
      intro X hX
      have hXA : X ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hX).1
      have hmX : m ∈ X := (Finset.mem_filter.mp hX).2
      have hsd : ∀ Y ∈ B.powerset,
          compatInd I ((A ∪ B) \ (X ∪ Y)) = compatInd I (A \ X) * compatInd I (B \ Y) :=
        fun Y hY => compatInd_sdiff_union_sdiff hXA (Finset.mem_powerset.mp hY) hAB hcross
      have h0 : (∅ : Finset V) ∈ B.powerset := Finset.mem_powerset.mpr (Finset.empty_subset B)
      have herase : (∑ Y ∈ B.powerset.erase (∅ : Finset V),
          ursell I (X ∪ Y) * compatInd I (B \ Y))
          = (if X = A then ursell I (A ∪ B) else 0) := by
        by_cases hXA' : X = A
        · rw [hXA', ite_eq_left rfl]
          rw [Finset.sum_eq_single B]
          · rw [Finset.sdiff_self, compatInd_empty, mul_one]
          · intro Y hY hne
            have hYmem : Y ∈ B.powerset := (Finset.mem_erase.mp hY).2
            have hYne : Y.Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hY).1
            have hYB : Y ⊆ B := Finset.mem_powerset.mp hYmem
            have hle : A ∪ Y ⊆ A ∪ B := Finset.union_subset_union (Finset.Subset.refl A) hYB
            have hlt : A ∪ Y ⊂ A ∪ B := by
              refine lt_of_le_of_ne hle ?_
              intro hEq
              have hc1 : (A ∪ Y).card = A.card + Y.card :=
                Finset.card_union_of_disjoint (hAB.mono (Finset.Subset.refl A) hYB)
              have hc2 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB
              have hcard_eq : (A ∪ Y).card = (A ∪ B).card := by rw [hEq]
              have hYle : Y.card ≤ B.card := Finset.card_le_card hYB
              exact hne (Finset.eq_of_subset_of_card_le hYB (by omega))
            rw [hvanish (Finset.Subset.refl A) hYB hmA hYne hlt, zero_mul]
          · intro h
            exact absurd (Finset.mem_erase.mpr
              ⟨hBne.ne_empty, Finset.mem_powerset.mpr (Finset.Subset.refl B)⟩) h
        · rw [ite_eq_right hXA']
          refine Finset.sum_eq_zero (fun Y hY => ?_)
          have hYmem : Y ∈ B.powerset := (Finset.mem_erase.mp hY).2
          have hYne : Y.Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hY).1
          have hYB : Y ⊆ B := Finset.mem_powerset.mp hYmem
          have hlt : X ∪ Y ⊂ A ∪ B := by
            refine lt_of_le_of_ne (Finset.union_subset_union hXA hYB) ?_
            intro hEq
            have hXYdisj : Disjoint X Y := hAB.mono hXA hYB
            have hc1 : (X ∪ Y).card = X.card + Y.card := Finset.card_union_of_disjoint hXYdisj
            have hc2 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB
            have hcard_eq : (X ∪ Y).card = (A ∪ B).card := by rw [hEq]
            have hXle : X.card ≤ A.card := Finset.card_le_card hXA
            have hYle : Y.card ≤ B.card := Finset.card_le_card hYB
            exact hXA' (Finset.eq_of_subset_of_card_le hXA (by omega))
          rw [hvanish hXA hYB hmX hYne hlt, zero_mul]
      have hstep1 : (∑ Y ∈ B.powerset, ursell I (X ∪ Y) * compatInd I ((A ∪ B) \ (X ∪ Y)))
          = ∑ Y ∈ B.powerset,
              compatInd I (A \ X) * (ursell I (X ∪ Y) * compatInd I (B \ Y)) :=
        Finset.sum_congr rfl (fun Y hY => by rw [hsd Y hY]; ring)
      rw [hstep1, ← Finset.mul_sum, ← Finset.sum_erase_add _ _ h0]
      simp only [Finset.union_empty, Finset.sdiff_empty]
      rw [herase]
      by_cases hXA' : X = A
      · rw [ite_eq_left hXA', hXA', Finset.sdiff_self, compatInd_empty, one_mul]
        ring
      · rw [ite_eq_right hXA']
        ring
    -- (4) 装配
    have hmin : A.min' hAne = m :=
      le_antisymm (Finset.min'_le A m hmA)
        (Finset.le_min' A hAne m (fun y hy => hmle y (Finset.mem_union_left B hy)))
    have h1 : (∑ T ∈ (A ∪ B).powerset.filter (fun T => m ∈ T),
        ursell I T * compatInd I ((A ∪ B) \ T))
        = ∑ X ∈ A.powerset.filter (fun X => m ∈ X),
            (compatInd I (A \ X) * (ursell I X * compatInd I B)
              + (if X = A then ursell I (A ∪ B) else 0)) := by
      rw [hdecomp]
      exact Finset.sum_congr rfl (fun X hX => hinner X hX)
    have hsplit : (∑ X ∈ A.powerset.filter (fun X => m ∈ X),
        (compatInd I (A \ X) * (ursell I X * compatInd I B)
          + (if X = A then ursell I (A ∪ B) else 0)))
        = (∑ X ∈ A.powerset.filter (fun X => m ∈ X),
            compatInd I (A \ X) * (ursell I X * compatInd I B))
          + ∑ X ∈ A.powerset.filter (fun X => m ∈ X),
              (if X = A then ursell I (A ∪ B) else 0) :=
      Finset.sum_add_distrib
    have hpart1 : (∑ X ∈ A.powerset.filter (fun X => m ∈ X),
        compatInd I (A \ X) * (ursell I X * compatInd I B))
        = compatInd I B * compatInd I A := by
      have hstep : (∑ X ∈ A.powerset.filter (fun X => m ∈ X),
          compatInd I (A \ X) * (ursell I X * compatInd I B))
          = ∑ X ∈ A.powerset.filter (fun X => m ∈ X),
              compatInd I B * (ursell I X * compatInd I (A \ X)) :=
        Finset.sum_congr rfl (fun X _ => by ring)
      rw [hstep, ← Finset.mul_sum]
      have hren := compatInd_eq_sum I hAne
      rw [hmin] at hren
      rw [← hren]
    have hpart2 : (∑ X ∈ A.powerset.filter (fun X => m ∈ X),
        (if X = A then ursell I (A ∪ B) else 0)) = ursell I (A ∪ B) := by
      rw [Finset.sum_eq_single A]
      · rw [ite_eq_left rfl]
      · intro X _ hne
        rw [ite_eq_right hne]
      · intro h
        exact absurd (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.Subset.refl A), hmA⟩) h
    have htotal : compatInd I (A ∪ B) = compatInd I (A ∪ B) + ursell I (A ∪ B) := by
      calc compatInd I (A ∪ B)
          = (∑ T ∈ (A ∪ B).powerset.filter (fun T => m ∈ T),
              ursell I T * compatInd I ((A ∪ B) \ T)) := hFULL.symm
        _ = compatInd I B * compatInd I A + ursell I (A ∪ B) := by
              rw [h1, hsplit, hpart1, hpart2]
        _ = compatInd I (A ∪ B) + ursell I (A ∪ B) := by
              rw [mul_comm, ← compatInd_union (A := A) (B := B) hcross]
    linarith [htotal]

/-- **引理 3.1 的"不连通 ⇒ `φ = 0`"（一般形式）**：`S = A ⊔ B`，`A`、`B` 非空不交、
`A` 与 `B` 横向相容 ⇒ `φ(S) = 0`（`B` 内部**可以**有边）。 -/
theorem ursell_eq_zero_of_split (I : SimpleGraph V) :
    ∀ S : Finset V, ∀ A B : Finset V, S = A ∪ B → Disjoint A B → A.Nonempty → B.Nonempty →
      (∀ a ∈ A, ∀ b ∈ B, ¬ I.Adj a b) → ursell I S = 0 := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro A B hS hAB hAne hBne hcross
    have hSne : S.Nonempty := hAne.mono (by rw [hS]; exact Finset.subset_union_left)
    by_cases hminA : S.min' hSne ∈ A
    · exact ursell_split_aux I S A B hS hAB hAne hBne hcross hSne hminA
    · have hminB : S.min' hSne ∈ B := by
        have hmem : S.min' hSne ∈ A ∪ B := hS ▸ Finset.min'_mem S hSne
        rcases Finset.mem_union.mp hmem with h | h
        · exact absurd h hminA
        · exact h
      refine ursell_split_aux I S B A ?_ hAB.symm hBne hAne ?_ hSne hminB
      · rw [hS, Finset.union_comm]
      · intro a ha b hb h
        exact hcross b hb a ha ((SimpleGraph.adj_comm I b a).mpr h)

end Pphi2Ursell
