import S6Isserlis.BlockModel
import S6Isserlis.GJ1841

/-!
# GJ 2nd ed `(18.4.1)` 的 **L3（分量数上界）+ 装配 T** —— M2 组合层第三块

来源（纸面）：`proofs/pphi2_gj_1841_general.md` §1.4（L3）、§1.5（T）；
书：Glimm–Jaffe, *Quantum Physics*, 2nd ed 印刷 p.368（PDF 384）。
方案：`formal/lean/M2_keystone18_plan.md` §4（定理清单）、§6（模块划分）。
前置：`s6/GJ1841.lean`（L1 森林界）、`s6/BlockModel.lean`（单位方格模型 + L2）。

## 内容

* `sqGraph_reachable_of_glue_component` —— 书的引理 **L2** 的字面形式：
  `glueGraph` 的连通分量所含方格，其方格图 `sqGraph` 连通。
* `card_connectedComponent_le_card_of_meets` —— 书的引理 **L3** 的一般形式：
  若图的每个连通分量都含 `S` 的一个顶点，则分量数 `≤ |S|`（书中 `r ≤ |X₀|` 取 `S = X₀`）。
* `gj_1841` —— 书 `(18.4.1)` 的**强化形式** `|X| − n ≤ |Γ|`（书的形式 `≤ 2|Γ|` 是其推论，
  见 `BlockModel.card_sub_one_le_two_mul_card`）；`gj_1841_enhanced` 是 `n = |X₀|` 的命名形式。

## 装配（书的 §1.5(b)，逐条对应）

```
|X| − n  ≤  |X| − r            (L3：r ≤ |X₀| ≤ n)
         ≤  #edges(sqGraph)    (L1 的逐分量形式和 = GJ1841.card_vert_sub_card_connectedComponent_le_card_edgeSet)
         =  |Γ ∩ Int X|        (边计数 card_linesIn_eq_card_edgeSet)
         ≤  |Γ|                (card_linesIn_le_card)
```

假设 **(i)**（每个 `X∖Γ^c` 的分量碰到 `X₀`）以 `glueGraph` 的分量表述 —— 这是 `BlockModel`
里"几何连通分量"的**已登记组合模型**；`glueGraph_reachable_iff_sqGraph_reachable`（书的 L2）把
(i) 从 `glueGraph` 分量搬到 `sqGraph` 分量上（`exists_mem_of_glue_component` 那一步）。

## 诚实边界

* **(H1)** `glueGraph` = "`X∖Γ^c` 的分量"是**模型口径**（`BlockModel` 文档已登记），非已证定理。
* **(H2)** 本文件（连同 `GJ1841.lean` / `BlockModel.lean`）**不**表示 `PPHI2_ACTIVITY_BOUND`
  （核 B）已闭合 —— `(18.4.1)` 只是**装配的记账步**，`(18.7.A)` 的合并记账仍 OPEN。
* **(H3)** 书的 §1.6 的**取等**（`Γ` = 生成树 ⇒ `|X| − n = |Γ|`）**未**形式化。
* **(H4)** 书里 `X₀` 的"承载 `n` 个外部点的方格并"这一层语义未建模；只用到 `|X₀| ≤ n` 与 (i)。
-/

noncomputable section
open scoped Classical
open scoped BigOperators
open SimpleGraph

namespace Pphi2Block

/-- **书的引理 L2 的字面形式**：`glueGraph` 的一个连通分量所含的方格，其方格图连通。

（`glueGraph` 的分量 = `X∖Γ^c` 的分量；`sqGraph` 的分量 = 方格图 `H`。这条正是
`proofs/pphi2_gj_1841_general.md` §1.3 的 L2，其证明内核在 `BlockModel` 的
`glueGraph_reachable_iff_sqGraph_reachable`。） -/
theorem sqGraph_reachable_of_glue_component (X : Finset Sq) (Γ : Finset Line)
    (hii : ∀ b ∈ Γ, b.sq1 ∈ X ∧ b.sq2 ∈ X)
    (C : (glueGraph X Γ).ConnectedComponent) {u v : {s : Sq // s ∈ X}}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) :
    (sqGraph X Γ).Reachable u v :=
  (glueGraph_reachable_iff_sqGraph_reachable X Γ hii u v).mp
    (SimpleGraph.ConnectedComponent.reachable_of_mem_supp C hu hv)

/-- "属于 `X₀` 的方格"，作为 `sqGraph X Γ` 顶点类型上的有限集。 -/
def sqOfMem (X X₀ : Finset Sq) : Finset {s : Sq // s ∈ X} :=
  Finset.univ.filter (fun s => s.1 ∈ X₀)

/-- `sqOfMem X X₀` 的势不超过 `X₀`（`s ↦ s.1` 是单射）。 -/
lemma card_sqOfMem_le (X X₀ : Finset Sq) : (sqOfMem X X₀).card ≤ X₀.card := by
  refine Finset.card_le_card_of_injOn (fun s : {s : Sq // s ∈ X} => s.1) ?_ ?_
  · intro s hs
    simpa [sqOfMem] using hs
  · intro a _ b _ hab
    exact Subtype.ext hab

/-- **书的引理 L3 的一般形式**：若图的每个连通分量都含 `S` 的一个顶点，则分量数 `≤ |S|`。

（分量两两不交 ⇒ 各取一个顶点给出单射。书中 `r ≤ |X₀|` 取 `S = X₀`。
用 `Nat.card` 而非 `Fintype.card` 陈述，以避开 `classical` 与 `instDecidableEq` 的实例菱形。） -/
theorem card_connectedComponent_le_card_of_meets {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (hi : ∀ C : G.ConnectedComponent, ∃ v : V, v ∈ C.supp ∧ v ∈ S) :
    Nat.card G.ConnectedComponent ≤ S.card := by
  classical
  choose f hf using hi
  have hinj : Function.Injective
      (fun C : G.ConnectedComponent => (⟨f C, (hf C).2⟩ : {x : V // x ∈ S})) := by
    intro C D hCD
    have h1 : f C = f D := by
      have h := congrArg (fun p : {x : V // x ∈ S} => (p : V)) hCD
      simpa using h
    have h2 : G.connectedComponentMk (f C) = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C (f C)).mp (hf C).1
    have h3 : G.connectedComponentMk (f D) = D :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff D (f D)).mp (hf D).1
    rw [← h2, ← h3, h1]
  have h := Fintype.card_le_of_injective
    (fun C : G.ConnectedComponent => (⟨f C, (hf C).2⟩ : {x : V // x ∈ S})) hinj
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_coe S] at h
  exact h

/-- 假设 (i) 从 `glueGraph` 的分量搬到 `sqGraph` 的分量（用书的 L2）。 -/
lemma exists_mem_of_glue_component {X X₀ : Finset Sq} {Γ : Finset Line}
    (hii : ∀ b ∈ Γ, b.sq1 ∈ X ∧ b.sq2 ∈ X)
    (hi : ∀ C : (glueGraph X Γ).ConnectedComponent,
      ∃ s : {s : Sq // s ∈ X}, s ∈ C.supp ∧ s.1 ∈ X₀) :
    ∀ C : (sqGraph X Γ).ConnectedComponent,
      ∃ s : {s : Sq // s ∈ X}, s ∈ C.supp ∧ s.1 ∈ X₀ := by
  intro C
  obtain ⟨s₀, hs₀⟩ := C.nonempty_supp
  obtain ⟨t, ht_mem, ht_X₀⟩ := hi ((glueGraph X Γ).connectedComponentMk s₀)
  refine ⟨t, ?_, ht_X₀⟩
  have hreach : (sqGraph X Γ).Reachable t s₀ :=
    (glueGraph_reachable_iff_sqGraph_reachable X Γ hii t s₀).mp
      (SimpleGraph.ConnectedComponent.reachable_of_mem_supp _
        ht_mem SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hs₀ ⊢
  rw [SimpleGraph.ConnectedComponent.sound hreach, hs₀]

set_option linter.style.haveILetI false in
/-- 书中 (i)（`glueGraph` 分量形式）+ L3 的合成：`sqGraph` 的分量数 `≤ |X₀|`。

`letI` 在这里是**必要**的（故关掉风格 linter）：`GJ1841` 的通用陈述在抽象类型上只能取
`Classical.propDecidable`，而具体类型 `↥X` 上 typeclass 会取到 `instDecidableEq`；两者不是 defeq 的，
`Fintype.card (·.ConnectedComponent)` 因此成为实例菱形。`letI`（值可展开）把局部实例钉成
`fun a b => Classical.propDecidable (a = b)`，从而 defeq 成立。 -/
theorem card_connectedComponent_le_card_of_glue_meets {X X₀ : Finset Sq} {Γ : Finset Line}
    (hii : ∀ b ∈ Γ, b.sq1 ∈ X ∧ b.sq2 ∈ X)
    (hi : ∀ C : (glueGraph X Γ).ConnectedComponent,
      ∃ s : {s : Sq // s ∈ X}, s ∈ C.supp ∧ s.1 ∈ X₀) :
    Nat.card (sqGraph X Γ).ConnectedComponent ≤ X₀.card := by
  -- 局部固定 `DecidableEq` 为经典实例：`GJ1841` 的通用陈述在抽象类型上只能用
  -- `Classical.propDecidable`，若不固定，本处会取到 `instDecidableEq` 而造成实例菱形。
  letI : DecidableEq {s : Sq // s ∈ X} := fun a b => Classical.propDecidable (a = b)
  have hmeets := exists_mem_of_glue_component hii hi
  have h : Nat.card (sqGraph X Γ).ConnectedComponent ≤ (sqOfMem X X₀).card :=
    card_connectedComponent_le_card_of_meets (sqGraph X Γ) (sqOfMem X X₀) (fun C => by
      obtain ⟨s, hs, hsX₀⟩ := hmeets C
      exact ⟨s, hs, by simpa [sqOfMem] using hsX₀⟩)
  exact h.trans (card_sqOfMem_le X X₀)

set_option linter.style.haveILetI false in
/-- **Glimm–Jaffe 2nd ed `(18.4.1)`（强化形式）**：`|X| − n ≤ |Γ|`。

假设 (i)：每个 `X∖Γ^c` 的连通分量（= `glueGraph` 的分量）都含 `X₀` 的一个方格；
假设 (ii)：`Γ ⊆ Int X`（每条 `Γ`-线的两个相邻方格都在 `X` 内）。

同样需要 `letI` 钉住 `DecidableEq ↥X`（理由见上一条的 docstring）。 -/
theorem gj_1841 {X X₀ : Finset Sq} {Γ : Finset Line} {n : ℕ}
    (hii : ∀ b ∈ Γ, b.sq1 ∈ X ∧ b.sq2 ∈ X)
    (hi : ∀ C : (glueGraph X Γ).ConnectedComponent,
      ∃ s : {s : Sq // s ∈ X}, s ∈ C.supp ∧ s.1 ∈ X₀)
    (hn : X₀.card ≤ n) :
    X.card - n ≤ Γ.card := by
  letI : DecidableEq {s : Sq // s ∈ X} := fun a b => Classical.propDecidable (a = b)
  have hk : Nat.card (sqGraph X Γ).ConnectedComponent ≤ X₀.card :=
    card_connectedComponent_le_card_of_glue_meets hii hi
  have h1 : Nat.card ↥X - Nat.card (sqGraph X Γ).ConnectedComponent
      ≤ Nat.card ↑(sqGraph X Γ).edgeSet := by
    rw [Nat.card_eq_fintype_card (α := (sqGraph X Γ).ConnectedComponent)]
    exact GJ1841.card_vert_sub_card_connectedComponent_le_card_edgeSet (sqGraph X Γ)
  have h3 : Nat.card ↑(sqGraph X Γ).edgeSet ≤ Γ.card := by
    rw [← card_linesIn_eq_card_edgeSet X Γ]
    exact card_linesIn_le_card X Γ
  have hcard : Nat.card ↥X = X.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe X]
  rw [hcard] at h1
  omega

/-- `(18.4.1)` 的命名形式：`|X| − |X₀| ≤ |Γ|`。 -/
theorem gj_1841_enhanced {X X₀ : Finset Sq} {Γ : Finset Line}
    (hii : ∀ b ∈ Γ, b.sq1 ∈ X ∧ b.sq2 ∈ X)
    (hi : ∀ C : (glueGraph X Γ).ConnectedComponent,
      ∃ s : {s : Sq // s ∈ X}, s ∈ C.supp ∧ s.1 ∈ X₀) :
    X.card - X₀.card ≤ Γ.card :=
  gj_1841 hii hi le_rfl

end Pphi2Block
