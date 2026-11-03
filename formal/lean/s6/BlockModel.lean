import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.Sym2

/-!
# 单位方格模型 + GJ 2nd ed `(18.4.1)` 的 **L2（角引理）**

来源：`proofs/pphi2_gj_1841_general.md` §1.1（记号）、§1.3（L2）；Glimm–Jaffe 2nd ed 印刷 p.360–364、p.368。
方案：`formal/lean/M2_keystone18_plan.md` §4/§6（模块 `BlockModel`）；前一块 L1 见 `s6/GJ1841.lean`。

## 模型（M2 方案 §6 的选项 (b)：组合口径）

* `Sq := ℤ × ℤ` 单位方格（按左下角索引）；`Line := ℤ × ℤ × Bool` 格线：
  `(i,j,false)` = 竖线 `{i}×[j,j+1]`（邻接 `(i-1,j)`、`(i,j)`），
  `(i,j,true)` = 横线 `[i,i+1]×{j}`（邻接 `(i,j-1)`、`(i,j)`）；每条线恰有两个相邻方格。
* `linesIn X Γ` = `Γ` 中两个相邻方格都在 `X` 内的线 = 书的 `Γ ∩ Int X`。
* `sqGraph X Γ` = 书的方格图 `H(X,Γ)`（边 = 共一条 `Γ`-线的方格对）。
* `glueGraph X Γ` = `sqGraph` 再加**角粘合**（共一格角 `c` 且 `c` 处四线全在 `Γ` 内）——
  即"`X∖Γ^c` 的连通分量"在方格层的组合模型。

## 机械化内容

`cornerLine_sq_mem`；**L2** `glueGraph_reachable_iff_sqGraph_reachable`（假设 (ii) `Γ ⊆ Int X`：
`glueGraph` 与 `sqGraph` 可达关系相同 —— 角引理 §1.3(a) 的组合内核，同时给出 §1.3(b)）；
`card_linesIn_eq_card_edgeSet`（边 = `Γ ∩ Int X`，用 `Line.toSym2` 单射）；
`card_sub_one_le_linesIn_of_connected` / `card_sub_one_le_two_mul_card`（L2 的计数推论 + `(18.4.1)` 第一式）。

## 诚实边界

* `glueGraph` **是**（而非**证明等于**）"`X∖Γ^c` 连通分量"的组合模型：§1.3(b) 的
  **ℝ² 拓扑**（闭方格挖边线段仍紧连通、连通集族之并连通 ⟺ 交叠图连通）**未**形式化
  （M2 方案 §6 选项 (b) 的**登记项**），故"分量 = 几何分量"属模型口径而非已证定理。
* 只到 L2。L3 与装配 T 在 `s6/GJ1841Block.lean`；三者合起来**不**表示
  `PPHI2_ACTIVITY_BOUND`（核 B）已闭合 —— `(18.7.A)` 的合并记账仍 OPEN。
-/

noncomputable section
open scoped Classical
open scoped BigOperators
open SimpleGraph

namespace Pphi2Block

/-- 单位方格，按左下角索引。 -/
abbrev Sq : Type := ℤ × ℤ

/-- 格线：`(i,j,false)` = 竖线 `{i} × [j,j+1]`，`(i,j,true)` = 横线 `[i,i+1] × {j}`。 -/
abbrev Line : Type := ℤ × ℤ × Bool

namespace Line

/-- 格线的第一个相邻方格。 -/
def sq1 : Line → Sq
  | (i, j, false) => (i - 1, j)
  | (i, j, true) => (i, j - 1)

/-- 格线的第二个相邻方格。 -/
def sq2 : Line → Sq
  | (i, j, false) => (i, j)
  | (i, j, true) => (i, j)

/-- 格线 `b` 与方格 `s` 相邻。 -/
def Adj (b : Line) (s : Sq) : Prop := s = b.sq1 ∨ s = b.sq2

/-- 一条格线的两个相邻方格互异。 -/
lemma sq1_ne_sq2 (b : Line) : b.sq1 ≠ b.sq2 := by
  obtain ⟨i, j, h⟩ := b
  cases h <;>
    · simp only [sq1, sq2]
      intro hh
      simp only [Prod.mk.injEq] at hh
      omega

/-- 格线作为无序点对。 -/
def toSym2 (b : Line) : Sym2 Sq := s(b.sq1, b.sq2)

/-- 格线由其无序点对决定。 -/
lemma toSym2_injective : Function.Injective toSym2 := by
  rintro ⟨i, j, h⟩ ⟨i', j', h'⟩ he
  cases h <;> cases h' <;>
    simp only [toSym2, sq1, sq2, Sym2.eq_iff] at he <;>
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [Prod.mk.injEq] at h1 h2 <;>
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    first
      | (show (i : ℤ) = i'; omega)
      | (show (j : ℤ) = j'; omega)
      | rfl
      | (exfalso; omega)

/-- 若相异的两方格都与同一条线相邻，则该线把它们按某一次序穷尽。 -/
lemma eq_sq_of_adj_adj_ne {b : Line} {x y : Sq} (hx : b.Adj x) (hy : b.Adj y)
    (hne : x ≠ y) :
    (b.sq1 = x ∧ b.sq2 = y) ∨ (b.sq1 = y ∧ b.sq2 = x) := by
  obtain ⟨i, j, h⟩ := b
  cases h
  · simp only [Adj, sq1, sq2] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hne
  · simp only [Adj, sq1, sq2] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hne

end Line

/-- 格角 `(x,y)` 处的四个单位方格。 -/
def cornerSquares (x y : ℤ) : Finset Sq :=
  {(x - 1, y - 1), (x, y - 1), (x - 1, y), (x, y)}

/-- 以格角 `(x,y)` 为端点的四条格线。 -/
def cornerLines (x y : ℤ) : Finset Line :=
  {(x, y - 1, false), (x, y, false), (x - 1, y, true), (x, y, true)}

/-- 角线的两个相邻方格都在该角的四个方格之内。 -/
lemma cornerLine_sq_mem {x y : ℤ} {b : Line} (hb : b ∈ cornerLines x y) :
    b.sq1 ∈ cornerSquares x y ∧ b.sq2 ∈ cornerSquares x y := by
  simp only [cornerLines, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;>
    simp [Line.sq1, Line.sq2, cornerSquares]

/-- `Γ` 中两个相邻方格都在 `X` 内的线（= 书的 `Γ ∩ Int X`）。 -/
def linesIn (X : Finset Sq) (Γ : Finset Line) : Finset Line :=
  Γ.filter (fun b => b.sq1 ∈ X ∧ b.sq2 ∈ X)

/-- 方格层到方格的强制（用于 `Sym2.map`）。 -/
def sqVal (X : Finset Sq) : {s : Sq // s ∈ X} → Sq := fun s => s.1

/-- `sqVal` 单射。 -/
lemma sqVal_injective (X : Finset Sq) : Function.Injective (sqVal X) :=
  fun _ _ h => Subtype.ext h

/-- 方格图的**线关系**：共一条 `Γ`-线的两个方格。 -/
def sqRel (X : Finset Sq) (Γ : Finset Line) (u v : {s : Sq // s ∈ X}) : Prop :=
  ∃ b : {b : Line // b ∈ Γ}, b.1.Adj u.1 ∧ b.1.Adj v.1

/-- 粘合图的**关系**：线关系，或"存活角"处共角的粘合。 -/
def glueRel (X : Finset Sq) (Γ : Finset Line) (u v : {s : Sq // s ∈ X}) : Prop :=
  (∃ b : {b : Line // b ∈ Γ}, b.1.Adj u.1 ∧ b.1.Adj v.1) ∨
    (∃ c : Sq, u.1 ∈ cornerSquares c.1 c.2 ∧ v.1 ∈ cornerSquares c.1 c.2 ∧
      ∀ b ∈ cornerLines c.1 c.2, b ∈ Γ)

/-- **方格图** `H(X, Γ)`。 -/
def sqGraph (X : Finset Sq) (Γ : Finset Line) : SimpleGraph {s : Sq // s ∈ X} :=
  SimpleGraph.fromRel (sqRel X Γ)

/-- **粘合图**：`sqGraph` 加上角粘合。 -/
def glueGraph (X : Finset Sq) (Γ : Finset Line) : SimpleGraph {s : Sq // s ∈ X} :=
  SimpleGraph.fromRel (glueRel X Γ)

/-- 线关系对称。 -/
lemma sqRel_symm {X : Finset Sq} {Γ : Finset Line} {u v : {s : Sq // s ∈ X}}
    (h : sqRel X Γ u v) : sqRel X Γ v u :=
  ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩

/-- 粘合关系对称。 -/
lemma glueRel_symm {X : Finset Sq} {Γ : Finset Line} {u v : {s : Sq // s ∈ X}}
    (h : glueRel X Γ u v) : glueRel X Γ v u := by
  rcases h with ⟨b, hu, hv⟩ | ⟨c, hu, hv, hall⟩
  · exact Or.inl ⟨b, hv, hu⟩
  · exact Or.inr ⟨c, hv, hu, hall⟩

/-- 方格图的邻接关系（线关系本已对称 ⇒ `fromRel` 的对称化不增加任何东西）。 -/
lemma sqGraph_adj_iff {X : Finset Sq} {Γ : Finset Line} {u v : {s : Sq // s ∈ X}} :
    (sqGraph X Γ).Adj u v ↔ u ≠ v ∧ sqRel X Γ u v := by
  rw [sqGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, h.elim id sqRel_symm⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-- 粘合图的邻接关系。 -/
lemma glueGraph_adj_iff {X : Finset Sq} {Γ : Finset Line} {u v : {s : Sq // s ∈ X}} :
    (glueGraph X Γ).Adj u v ↔ u ≠ v ∧ glueRel X Γ u v := by
  rw [glueGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, h.elim id glueRel_symm⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-- `sqGraph` 是 `glueGraph` 的子图。 -/
lemma sqGraph_le_glueGraph (X : Finset Sq) (Γ : Finset Line) :
    sqGraph X Γ ≤ glueGraph X Γ := by
  intro u v h
  rw [sqGraph_adj_iff] at h
  rw [glueGraph_adj_iff]
  exact ⟨h.1, Or.inl h.2⟩

/-- 共 `Γ`-线且相异的两个方格在 `sqGraph` 中相邻。 -/
lemma sqGraph_adj_of_adj {X : Finset Sq} {Γ : Finset Line} {l : Line} (hl : l ∈ Γ)
    {p q : {s : Sq // s ∈ X}} (hp : l.Adj p.1) (hq : l.Adj q.1) (hne : p ≠ q) :
    (sqGraph X Γ).Adj p q := by
  rw [sqGraph_adj_iff]
  exact ⟨hne, ⟨l, hl⟩, hp, hq⟩

/-- `p`、`q` 恰为 `l` 的两个相邻方格 ⇒ 在 `sqGraph` 中相邻（相异性自动）。 -/
lemma sqGraph_adj_of_line {X : Finset Sq} {Γ : Finset Line} {l : Line} (hl : l ∈ Γ)
    {p q : {s : Sq // s ∈ X}} (hp : p.1 = l.sq1) (hq : q.1 = l.sq2) :
    (sqGraph X Γ).Adj p q := by
  rw [sqGraph_adj_iff]
  refine ⟨?_, ⟨l, hl⟩, Or.inl hp, Or.inr hq⟩
  intro hpq
  have h1 : p.1 = q.1 := congrArg Subtype.val hpq
  rw [hp, hq] at h1
  exact Line.sq1_ne_sq2 l h1

/-- **角引理 §1.3(a) 的组合内核**：在 (ii) 下，共一个"存活角"的方格在 `sqGraph` 中可达。 -/
lemma sqGraph_reachable_of_corner {X : Finset Sq} {Γ : Finset Line} {c : Sq}
    (hii : ∀ b ∈ Γ, b.sq1 ∈ X ∧ b.sq2 ∈ X)
    (hall : ∀ b ∈ cornerLines c.1 c.2, b ∈ Γ)
    {u v : {s : Sq // s ∈ X}}
    (hu : u.1 ∈ cornerSquares c.1 c.2) (hv : v.1 ∈ cornerSquares c.1 c.2) :
    (sqGraph X Γ).Reachable u v := by
  have hl1 : (c.1, c.2 - 1, false) ∈ Γ := hall _ (by simp [cornerLines])
  have hl2 : (c.1, c.2, true) ∈ Γ := hall _ (by simp [cornerLines])
  have hl3 : (c.1 - 1, c.2, true) ∈ Γ := hall _ (by simp [cornerLines])
  have h0X : (c.1 - 1, c.2 - 1) ∈ X := (hii _ hl1).1
  have h1X : (c.1, c.2 - 1) ∈ X := (hii _ hl1).2
  let h0 : {s : Sq // s ∈ X} := ⟨(c.1 - 1, c.2 - 1), h0X⟩
  let h1 : {s : Sq // s ∈ X} := ⟨(c.1, c.2 - 1), h1X⟩
  have key : ∀ p : {s : Sq // s ∈ X}, p.1 ∈ cornerSquares c.1 c.2 →
      (sqGraph X Γ).Reachable p h0 := by
    intro p hp
    simp only [cornerSquares, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp | hp
    · have hpe : p = h0 := Subtype.ext hp
      exact Eq.mpr (congrArg (fun x : {s : Sq // s ∈ X} => (sqGraph X Γ).Reachable x h0)
        hpe) (SimpleGraph.Reachable.refl h0)
    · exact (sqGraph_adj_of_line hl1 (p := h0) (q := p) rfl hp).reachable.symm
    · exact (sqGraph_adj_of_line hl3 (p := h0) (q := p) rfl hp).reachable.symm
    · exact ((sqGraph_adj_of_line hl2 (p := h1) (q := p) rfl hp).reachable.symm).trans
        ((sqGraph_adj_of_line hl1 (p := h0) (q := h1) rfl rfl).reachable.symm)
  exact (key u hu).trans (key v hv).symm

/-- 粘合步在 `sqGraph` 中的可达性（L2(a) 的单步形式）。 -/
lemma reachable_of_glue_adj {X : Finset Sq} {Γ : Finset Line}
    (hii : ∀ b ∈ Γ, b.sq1 ∈ X ∧ b.sq2 ∈ X)
    {a b : {s : Sq // s ∈ X}} (h : (glueGraph X Γ).Adj a b) :
    Relation.ReflTransGen (sqGraph X Γ).Adj a b := by
  rw [glueGraph_adj_iff] at h
  obtain ⟨hne, hstep⟩ := h
  rcases hstep with ⟨l, ha, hb⟩ | ⟨c, ha, hb, hall⟩
  · exact (SimpleGraph.reachable_iff_reflTransGen a b).mp
      (sqGraph_adj_of_adj l.2 ha hb hne).reachable
  · exact (SimpleGraph.reachable_iff_reflTransGen a b).mp
      (sqGraph_reachable_of_corner hii hall ha hb)

/-- **L2（角引理）**：在 (ii) 下 `glueGraph` 与 `sqGraph` 有相同的可达关系。 -/
theorem glueGraph_reachable_iff_sqGraph_reachable (X : Finset Sq) (Γ : Finset Line)
    (hii : ∀ b ∈ Γ, b.sq1 ∈ X ∧ b.sq2 ∈ X) (u v : {s : Sq // s ∈ X}) :
    (glueGraph X Γ).Reachable u v ↔ (sqGraph X Γ).Reachable u v := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    rw [SimpleGraph.reachable_iff_reflTransGen]
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.trans (reachable_of_glue_adj hii hbc)
  · intro h
    exact SimpleGraph.Reachable.mono (sqGraph_le_glueGraph X Γ) h

/-! ### 边计数 -/

/-- `Sym2.map` 保持单射。 -/
lemma sym2_map_injective {α β : Type*} {g : α → β} (hg : Function.Injective g) :
    Function.Injective (Sym2.map g) := by
  intro a b
  refine Sym2.inductionOn (f := fun i => Sym2.map g i = Sym2.map g b → i = b) a ?_
  intro x y
  refine Sym2.inductionOn (f := fun j => Sym2.map g s(x, y) = Sym2.map g j → s(x, y) = j) b ?_
  intro z w hab
  rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at hab
  rw [Sym2.eq_iff]
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hg h1, hg h2⟩
  · exact Or.inr ⟨hg h1, hg h2⟩

/-- 图的边数（`edgeFinset`）与边集势一致。 -/
lemma edgeFinset_card_eq_natCard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card = Nat.card ↑G.edgeSet := by
  rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]

/-- **边 = `Γ ∩ Int X`**：`linesIn X Γ` 与 `sqGraph X Γ` 的边集等势。 -/
theorem card_linesIn_eq_card_edgeSet (X : Finset Sq) (Γ : Finset Line) :
    (linesIn X Γ).card = Nat.card ↑(sqGraph X Γ).edgeSet := by
  classical
  have hg : Function.Injective (fun s : {s : Sq // s ∈ X} => s.1) :=
    fun _ _ h => Subtype.ext h
  have hsub1 : (linesIn X Γ).image Line.toSym2 ⊆
      (sqGraph X Γ).edgeFinset.image (Sym2.map (fun s : {s : Sq // s ∈ X} => s.1)) := by
    intro e he
    rw [Finset.mem_image] at he ⊢
    obtain ⟨b, hb, rfl⟩ := he
    obtain ⟨hbΓ, hb1, hb2⟩ := Finset.mem_filter.mp hb
    refine ⟨s(⟨b.sq1, hb1⟩, ⟨b.sq2, hb2⟩), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sqGraph_adj_iff]
      refine ⟨?_, ⟨⟨b, hbΓ⟩, Or.inl rfl, Or.inr rfl⟩⟩
      intro h
      exact Line.sq1_ne_sq2 b (by simpa using congrArg Subtype.val h)
    · simp only [Sym2.map_mk, Line.toSym2]
  have hsub2 : (sqGraph X Γ).edgeFinset.image (Sym2.map (fun s : {s : Sq // s ∈ X} => s.1)) ⊆
      (linesIn X Γ).image Line.toSym2 := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    revert he'
    refine Sym2.inductionOn (f := fun e' => e' ∈ (sqGraph X Γ).edgeFinset →
      Sym2.map (fun s : {s : Sq // s ∈ X} => s.1) e' ∈ (linesIn X Γ).image Line.toSym2) e' ?_
    intro u v he'
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sqGraph_adj_iff] at he'
    obtain ⟨hne, b, hbu, hbv⟩ := he'
    have hne' : u.1 ≠ v.1 := fun h => hne (Subtype.ext h)
    rw [Sym2.map_mk, Finset.mem_image]
    rcases Line.eq_sq_of_adj_adj_ne hbu hbv hne' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨b.1, ?_, ?_⟩
      · rw [linesIn, Finset.mem_filter]
        exact ⟨b.2, by rw [h1]; exact u.2, by rw [h2]; exact v.2⟩
      · simp only [Line.toSym2, h1, h2]
    · refine ⟨b.1, ?_, ?_⟩
      · rw [linesIn, Finset.mem_filter]
        exact ⟨b.2, by rw [h1]; exact v.2, by rw [h2]; exact u.2⟩
      · simp only [Line.toSym2, Sym2.eq_iff]
        exact Or.inr ⟨h1, h2⟩
  calc (linesIn X Γ).card
      = ((linesIn X Γ).image Line.toSym2).card :=
        (Finset.card_image_of_injective _ Line.toSym2_injective).symm
    _ = ((sqGraph X Γ).edgeFinset.image
          (Sym2.map (fun s : {s : Sq // s ∈ X} => s.1))).card := by
        rw [Finset.Subset.antisymm hsub1 hsub2]
    _ = (sqGraph X Γ).edgeFinset.card :=
        Finset.card_image_of_injective _ (sym2_map_injective hg)
    _ = Nat.card ↑(sqGraph X Γ).edgeSet := edgeFinset_card_eq_natCard _

/-- `Γ ∩ Int X ⊆ Γ`。 -/
theorem card_linesIn_le_card (X : Finset Sq) (Γ : Finset Line) :
    (linesIn X Γ).card ≤ Γ.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- **L2 的计数推论**：连通方格集 `Y` 满足 `|Y| − 1 ≤ |Γ ∩ Int Y|`。 -/
theorem card_sub_one_le_linesIn_of_connected {Y : Finset Sq} {Γ : Finset Line}
    (hconn : (sqGraph Y Γ).Connected) :
    Y.card - 1 ≤ (linesIn Y Γ).card := by
  have h1 : Nat.card {s : Sq // s ∈ Y} ≤ Nat.card ↑(sqGraph Y Γ).edgeSet + 1 :=
    hconn.card_vert_le_card_edgeSet_add_one
  rw [← card_linesIn_eq_card_edgeSet Y Γ, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  omega

/-- **书的 `(18.4.1)` 第一式**：`|Y| − 1 ≤ 2|Γ|`（对连通 `Y`）。 -/
theorem card_sub_one_le_two_mul_card {Y : Finset Sq} {Γ : Finset Line}
    (hconn : (sqGraph Y Γ).Connected) :
    Y.card - 1 ≤ 2 * Γ.card := by
  have h1 := card_sub_one_le_linesIn_of_connected hconn
  have h2 := card_linesIn_le_card Y Γ
  omega

end Pphi2Block
