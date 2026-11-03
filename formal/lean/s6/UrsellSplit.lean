/-
Ursell/Mayer 组合核的**第二块** —— 引理 3.1（连通性引理）中
**"不可相容图不连通 ⇒ `φ = 0`"那一半的一个真情形**：**单点可剥离**。

**口径**：见 `UrsellCore.lean` 的文件头（`proofs/pphi2_cluster_expansion.md` 的 `(2.2)` 递推、
相容集 = 不可相容图 `I` 的独立集、`φ(∅) = 0`）。

**本文件证了什么**

1. `compatInd_union`：**相容性指示子在"横向相容的不交并"下可乘** ——
   `[A ∪ B 相容] = [A 相容]·[B 相容]`（只要 `A` 与 `B` 之间没有不可相容边）。
2. `ursell_insert_eq_zero`：**单点可剥离情形** —— 若 `b ∉ A`、`A` 非空、且 `b` 与 `A` 中
   每个元素都相容，则 `φ(A ∪ {b}) = 0`。这是引理 3.1 的一个真情形（此时 `{b}` 是 `𝕀(A∪{b})`
   的一个连通分量，图不连通）；证明只用 `(2.2)` 的续接方程 + 本文件的乘性 + 对 `A` 的强归纳。
3. `ursell_union_singleton_eq_zero`：上面那条的对外形式（`A ∪ {b}`）。

**明确不在本文件内**（诚实边界）：

* 引理 3.1 的**一般形式**（`S = A ⊔ B` 横向相容、`|B| ≥ 2`，即 `B` 内部**可以**有边）；
* 引理 3.1 的**另一半**（`𝕀` 连通 ⇒ `φ ≠ 0`）；
* 定理 3.2（连通图公式）与定理 3.3（树图界）；`(2.1)` 指数公式的形式幂级数路线。
-/
import S6Isserlis.UrsellCore
import Mathlib.Tactic

noncomputable section

open scoped Classical
open Finset

namespace Pphi2Ursell

variable {V : Type*} [LinearOrder V]

/-! ### §4 相容性指示子的乘性 -/

/-- 单元素集的相容性指示子恒为 `1`（无自环口径）。 -/
@[simp] theorem compatInd_singleton {V : Type*} {I : SimpleGraph V} (i : V) :
    compatInd I {i} = 1 := by
  rw [compatInd, ite_eq_left (isCompatible_singleton I i)]

/-- **相容性指示子在"横向相容的不交并"下可乘**：只要 `A` 与 `B` 之间没有不可相容边，
`[A ∪ B 相容] = [A 相容]·[B 相容]`（ℤ 值）。

> 注意：显式带 `[DecidableEq V]`（而不是靠 `[LinearOrder V]` 的自动实例）——
> 否则 `A ∪ B` 的 `Finset.union` 实例会随调用上下文变化，与上下文里的项**不 defeq**。 -/
theorem compatInd_union {V : Type*} [DecidableEq V] {I : SimpleGraph V} {A B : Finset V}
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ I.Adj a b) :
    compatInd I (A ∪ B) = compatInd I A * compatInd I B := by
  rw [compatInd, compatInd, compatInd]
  by_cases hAB : IsCompatible I (A ∪ B)
  · rw [ite_eq_left hAB, ite_eq_left (hAB.mono Finset.subset_union_left),
      ite_eq_left (hAB.mono Finset.subset_union_right), one_mul]
  · rw [ite_eq_right hAB]
    by_cases hA : IsCompatible I A
    · have hB : ¬ IsCompatible I B := by
        intro hB
        refine hAB ?_
        intro u hu v hv huv
        rw [Finset.mem_union] at hu hv
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact hA u hu v hv huv
        · exact hcross u hu v hv
        · exact fun h => hcross v hv u hu ((SimpleGraph.adj_comm I v u).mpr h)
        · exact hB u hu v hv huv
      rw [ite_eq_left hA, ite_eq_right hB, mul_zero]
    · rw [ite_eq_right hA, zero_mul]

/-! ### §5 引理 3.1 的单点可剥离情形 -/

/-- `insert b A` 中不含 `b` 的子集必含于 `A`。 -/
private theorem subset_of_subset_insert {A A' : Finset V} {b : V}
    (h : A' ⊆ insert b A) (hb : b ∉ A') : A' ⊆ A := by
  intro x hx
  rcases Finset.mem_insert.mp (h hx) with rfl | hx'
  · exact absurd hx hb
  · exact hx'

/-- **单点可剥离 ⇒ `φ = 0`**：`b ∉ A`、`A` 非空、`b` 与 `A` 中每个元素相容 ⇒ `φ(A∪{b}) = 0`。 -/
private theorem ursell_insert_eq_zero (I : SimpleGraph V) :
    ∀ A : Finset V, A.Nonempty → ∀ b : V, b ∉ A → (∀ a ∈ A, ¬ I.Adj a b) →
      ursell I (insert b A) = 0 := by
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    intro hAne b hbA hcross
    have hSne : (insert b A : Finset V).Nonempty := ⟨b, Finset.mem_insert_self b A⟩
    have hbS : b ∈ (insert b A : Finset V) := Finset.mem_insert_self b A
    have hAS : A ⊆ (insert b A : Finset V) := Finset.subset_insert b A
    -- `compatInd` 乘性
    have hScomp : compatInd I (insert b A : Finset V) = compatInd I A := by
      rw [← Finset.union_singleton, compatInd_union (A := A) (B := {b}) (fun a ha x hx => by
        rw [Finset.mem_singleton] at hx
        subst hx
        exact hcross a ha), compatInd_singleton, mul_one]
    rw [ursell_eq_of_nonempty I hSne]
    set m := (insert b A : Finset V).min' hSne with hmdef
    have hmS : m ∈ (insert b A : Finset V) := by
      rw [hmdef]
      exact Finset.min'_mem _ _
    have hmle : ∀ x ∈ (insert b A : Finset V), m ≤ x := by
      intro x hx
      rw [hmdef]
      exact Finset.min'_le _ x hx
    -- 含 `b` 的项都可用归纳假设杀掉（需要 `T \ {b}` 非空）
    have hvanish : ∀ T ∈ (insert b A : Finset V).powerset.filter
        (fun T => m ∈ T ∧ T ≠ (insert b A : Finset V)), b ∈ T → (T \ {b}).Nonempty →
        ursell I T * compatInd I ((insert b A : Finset V) \ T) = 0 := by
      intro T hT hbT hne'
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      obtain ⟨hsub, -, hTS⟩ := hT
      have hTeq : T = insert b (T \ {b}) := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.insert_erase hbT]
      have hsub' : T \ {b} ⊆ A :=
        subset_of_subset_insert (Finset.sdiff_subset.trans hsub) (by simp)
      have hlt : T \ {b} ⊂ A := by
        refine lt_of_le_of_ne hsub' ?_
        intro hEq
        exact hTS (by rw [hTeq, hEq])
      rw [hTeq, ih (T \ {b}) hlt hne' b (by simp) (fun a ha => hcross a (hsub' ha)), zero_mul]
    have hkey : ∑ T ∈ (insert b A : Finset V).powerset.filter
        (fun T => m ∈ T ∧ T ≠ (insert b A : Finset V)),
        ursell I T * compatInd I ((insert b A : Finset V) \ T) = compatInd I A := by
      by_cases hmb : m = b
      · -- 情形 1：`m = b` ⇒ 只有 `T = {b}` 一项
        rw [Finset.sum_eq_single ({b} : Finset V)]
        · have hsb : (insert b A : Finset V) \ ({b} : Finset V) = A := by
            rw [Finset.sdiff_singleton_eq_erase, Finset.erase_insert hbA]
          rw [hsb, ursell_singleton I b, one_mul]
        · intro T hT hne
          have hbT : b ∈ T := by rw [← hmb]; exact (Finset.mem_filter.mp hT).2.1
          have hne' : (T \ {b}).Nonempty := by
            obtain ⟨a, haT, hab⟩ : ∃ a ∈ T, a ≠ b := by
              by_contra h
              push Not at h
              exact hne (Finset.eq_singleton_iff_unique_mem.mpr ⟨hbT, h⟩)
            exact ⟨a, Finset.mem_sdiff.mpr ⟨haT, by simpa using hab⟩⟩
          exact hvanish T hT hbT hne'
        · intro h
          exfalso
          refine h ?_
          rw [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.singleton_subset_iff.mpr hbS, by rw [hmb]; exact Finset.mem_singleton_self b,
            fun hEq => ?_⟩
          obtain ⟨a, ha⟩ := hAne
          have ha' : a ∈ ({b} : Finset V) := by rw [hEq]; exact Finset.mem_insert_of_mem ha
          exact hbA (by rw [← Finset.mem_singleton.mp ha']; exact ha)
      · -- 情形 2：`m ≠ b` ⇒ `m ∈ A`
        have hmA : m ∈ A := by
          rcases Finset.mem_insert.mp hmS with h | h
          · exact absurd h hmb
          · exact h
        -- 去掉含 `b` 的项后，索引集恰是 `A.powerset.filter (m ∈ ·)`
        have hEq1 : ((insert b A : Finset V).powerset.filter
              (fun T => m ∈ T ∧ T ≠ (insert b A : Finset V))).filter (fun T => b ∉ T)
            = A.powerset.filter (fun T => m ∈ T) := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_powerset]
          constructor
          · rintro ⟨⟨hsub, hmT, -⟩, hbT⟩
            exact ⟨subset_of_subset_insert hsub hbT, hmT⟩
          · rintro ⟨hsub, hmT⟩
            refine ⟨⟨hsub.trans hAS, hmT,
              fun hEq => hbA (hsub (by rw [hEq]; exact hbS))⟩, ?_⟩
            intro hbT
            exact hbA (hsub hbT)
        -- `(insert b A) \ T = (A \ T) ∪ {b}`（`T ⊆ A`、`b ∉ A`）
        have hsdiff : ∀ T ∈ A.powerset.filter (fun T => m ∈ T),
            (insert b A : Finset V) \ T = (A \ T) ∪ ({b} : Finset V) := by
          intro T hT
          have hsub : T ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
          have hbT : b ∉ T := fun h => hbA (hsub h)
          rw [Finset.insert_sdiff_of_notMem A hbT, ← Finset.union_singleton b (A \ T)]
        -- 乘性把 `[(A∖T) ∪ {b} 相容]` 化成 `[A∖T 相容]`
        have hstep3 : ∀ T ∈ A.powerset.filter (fun T => m ∈ T),
            compatInd I ((A \ T) ∪ ({b} : Finset V)) = compatInd I (A \ T) := by
          intro T hT
          rw [compatInd_union (A := A \ T) (B := {b}) (fun a ha x hx => by
            rw [Finset.mem_singleton] at hx
            subst hx
            exact hcross a (Finset.mem_sdiff.mp ha).1), compatInd_singleton, mul_one]
        -- `min' A = m`，于是剩下的和就是 `A` 的续接方程
        have hminA : A.min' hAne = m :=
          le_antisymm (Finset.min'_le A m hmA)
            (Finset.le_min' A hAne m (fun y hy => hmle y (hAS hy)))
        -- 含 `b` 的项全为 0，故可先换成"去掉含 `b` 的项"的和
        have hstep1 : ∑ T ∈ (insert b A : Finset V).powerset.filter
              (fun T => m ∈ T ∧ T ≠ (insert b A : Finset V)),
              ursell I T * compatInd I ((insert b A : Finset V) \ T)
            = ∑ T ∈ ((insert b A : Finset V).powerset.filter
              (fun T => m ∈ T ∧ T ≠ (insert b A : Finset V))).filter (fun T => b ∉ T),
              ursell I T * compatInd I ((insert b A : Finset V) \ T) := by
          rw [Finset.sum_filter (s := (insert b A : Finset V).powerset.filter
            (fun T => m ∈ T ∧ T ≠ (insert b A : Finset V))) (p := fun T => b ∉ T)]
          refine Finset.sum_congr rfl ?_
          intro T hT
          by_cases hbT : b ∈ T
          · rw [ite_eq_right (by simpa using hbT),
              hvanish T hT hbT ⟨m, Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hT).2.1,
                by rw [Finset.mem_singleton]; exact hmb⟩⟩]
          · rw [ite_eq_left (by simpa using hbT)]
        rw [hstep1, hEq1]
        rw [Finset.sum_congr rfl (fun T hT => by rw [hsdiff T hT, hstep3 T hT])]
        rw [← hminA]
        exact (compatInd_eq_sum I hAne).symm
    rw [hkey, hScomp]
    ring

/-- **引理 3.1 的"单点可剥离 ⇒ `φ = 0`"**（对外形式）：`b ∉ A`、`A` 非空、
`b` 与 `A` 中每个元素相容 ⇒ `φ(A ∪ {b}) = 0`。 -/
theorem ursell_union_singleton_eq_zero (I : SimpleGraph V) {A : Finset V} {b : V}
    (hA : A.Nonempty) (hbA : b ∉ A) (hcross : ∀ a ∈ A, ¬ I.Adj a b) :
    ursell I (A ∪ {b}) = 0 := by
  rw [Finset.union_singleton]
  exact ursell_insert_eq_zero I A hA b hbA hcross

/-- `A ∪ B = (A ∪ (B ∖ {b})) ∪ {b}`（`b ∈ B`）。 -/
private theorem union_eq_union_sdiff_singleton {A B : Finset V} {b : V} (hb : b ∈ B) :
    A ∪ B = (A ∪ (B \ {b})) ∪ {b} := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro (hx | hx)
    · exact Or.inl (Or.inl hx)
    · by_cases hxb : x = b
      · exact Or.inr hxb
      · exact Or.inl (Or.inr ⟨hx, hxb⟩)
  · rintro ((hx | hx) | hx)
    · exact Or.inl hx
    · exact Or.inr hx.1
    · rw [hx]; exact Or.inr hb

/-- **引理 3.1 的"不连通 ⇒ `φ = 0`"（右侧独立的情形）**：`S = A ⊔ B`，`A`、`B` 非空不交、
`B` **相容**（内部无边）、`A` 与 `B` 横向相容 ⇒ `φ(S) = 0`。
证明 = 把 `B` 的元素逐个用「单点可剥离」剥掉。 -/
theorem ursell_union_eq_zero_of_isCompatible_right (I : SimpleGraph V) {A B : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B) (hcomp : IsCompatible I B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ I.Adj a b) : ursell I (A ∪ B) = 0 := by
  obtain ⟨b, hbB⟩ := hB
  have hbA' : b ∉ A ∪ (B \ {b}) := by
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    rintro (h | ⟨-, hb'⟩)
    · exact Finset.disjoint_left.mp hAB h hbB
    · exact hb' rfl
  have hne' : (A ∪ (B \ {b})).Nonempty := hA.mono Finset.subset_union_left
  have hcross' : ∀ a ∈ A ∪ (B \ {b}), ¬ I.Adj a b := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hcross a ha b hbB
    · obtain ⟨haB, hab⟩ := Finset.mem_sdiff.mp ha
      rw [Finset.mem_singleton] at hab
      exact hcomp a haB b hbB hab
  rw [union_eq_union_sdiff_singleton hbB]
  exact ursell_union_singleton_eq_zero I hne' hbA' hcross'

end Pphi2Ursell
