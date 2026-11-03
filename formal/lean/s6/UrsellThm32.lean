import S6Isserlis.UrsellConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

noncomputable section

open scoped Classical
open Finset

namespace Pphi2Ursell

variable {V : Type*} [LinearOrder V]

/-! ### §13 "最小元所在连通分量"：可及集刻画 -/

/-- `F` 下从 `m` 出发可及的顶点，**限制在 `S` 内**。 -/
def reachSet (F : Finset (Sym2 V)) (S : Finset V) (m : V) : Finset V :=
  S.filter (fun x => (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable m x)

omit [LinearOrder V] in
@[simp] theorem mem_reachSet {F : Finset (Sym2 V)} {S : Finset V} {m x : V} :
    x ∈ reachSet F S m ↔ x ∈ S ∧
      (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable m x := by
  simp [reachSet]

omit [LinearOrder V] in
theorem reachSet_mono {F F' : Finset (Sym2 V)} (h : F ⊆ F') {S : Finset V} {m x : V}
    (hx : x ∈ reachSet F S m) : x ∈ reachSet F' S m := by
  rw [mem_reachSet] at hx ⊢
  exact ⟨hx.1, hx.2.mono (by
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab ⊢
    exact ⟨h hab.1, hab.2⟩)⟩

omit [LinearOrder V] in
/-- `edgeWithin I S` 的每个成员的两端点都在 `S` 内。 -/
theorem mem_of_mem_edgeWithin {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    {e : Sym2 V} (he : e ∈ edgeWithin I S) : ∀ v ∈ e, v ∈ S :=
  (Finset.mem_filter.mp (show e ∈ I.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S) from he)).2

omit [LinearOrder V] in
/-- **走步留在 `S` 内**：`F ⊆ edgeWithin I S` 且走步从 `m ∈ S` 出发 ⇒ 终点在 `S` 内。 -/
theorem mem_of_reachable_of_subset_edgeWithin {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S)
    {x : V} (hx : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable m x) : x ∈ S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hx
  induction hx with
  | refl => exact hm
  | tail _ hadj _ =>
    rename_i a b _ _
    have hmem : s(a, b) ∈ F := by
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      exact hadj.1
    exact mem_of_mem_edgeWithin (hF hmem) b (Sym2.mem_iff.mpr (Or.inr rfl))

omit [LinearOrder V] in
/-- `m ∈ S` ⇒ `m ∈ reachSet F S m`（可及性自反）。 -/
@[simp] theorem self_mem_reachSet {F : Finset (Sym2 V)} {S : Finset V} {m : V} (hm : m ∈ S) :
    m ∈ reachSet F S m := by
  rw [mem_reachSet]
  exact ⟨hm, SimpleGraph.Reachable.refl _⟩

omit [LinearOrder V] in
/-- `reachSet F S m ⊆ S`。 -/
theorem reachSet_subset {F : Finset (Sym2 V)} {S : Finset V} {m : V} :
    reachSet F S m ⊆ S := fun _ hx => (mem_reachSet.mp hx).1

omit [LinearOrder V] in
/-- `m ∈ S` ⇒ `reachSet F S m` 非空。 -/
theorem reachSet_nonempty {F : Finset (Sym2 V)} {S : Finset V} {m : V} (hm : m ∈ S) :
    (reachSet F S m).Nonempty := ⟨m, self_mem_reachSet hm⟩

omit [LinearOrder V] in
/-- 走步的每个顶点（起点、终点、或中间经过的）都与起点可及。

这里不走 `p.support`（其 `nil` 情形涉及 `List` 强转，易踩坑），
而是直接用 `Walk` 的递归结构：`cons` 的头顶点与尾走步的顶点。 -/
theorem reachable_of_mem_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    {x : V} (hx : x ∈ p.support) : G.Reachable u x := by
  induction p with
  | nil =>
    rw [SimpleGraph.Walk.support_nil] at hx
    rw [List.mem_singleton] at hx
    exact hx ▸ SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    rw [SimpleGraph.Walk.support_cons] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact SimpleGraph.Reachable.refl _
    · exact (SimpleGraph.Adj.reachable hadj).trans (ih hx)

omit [LinearOrder V] in
/-- **`F` 下从 `m` 可及的顶点集在 `F` 下连通**（诱导子图口径）。
`F ⊆ edgeWithin I S`、`m ∈ S` ⇒ `reachSet F S m` 上由 `F` 生成的诱导图连通。
供蓝图"满射"步使用。 -/
theorem connected_induce_reachSet {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S) :
    ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce
      (↑(reachSet F S m) : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨m, (mem_reachSet (F := F) (S := S) (m := m) (x := m)).mpr
    ⟨hm, SimpleGraph.Reachable.refl _⟩⟩, fun w => ?_⟩
  obtain ⟨hwr⟩ := (mem_reachSet.mp w.2).2
  refine ⟨hwr.induce _ (fun x hx => ?_)⟩
  exact (mem_reachSet (F := F) (S := S) (m := m) (x := x)).mpr
    ⟨mem_of_reachable_of_subset_edgeWithin hF hm (reachable_of_mem_support hwr hx),
      reachable_of_mem_support hwr hx⟩

/-! ### §14 `edgeWithin` 与子集的相容性 -/

omit [LinearOrder V] in
/-- `A ⊆ S` 时，`edgeWithin I A` 恰是 `edgeWithin I S` 中"两端点都落在 `A`"的那些边。 -/
theorem edgeWithin_eq_filter {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {A S : Finset V} (hAS : A ⊆ S) :
    edgeWithin I A = (edgeWithin I S).filter (fun e => ∀ v ∈ e, v ∈ A) := by
  ext e
  simp only [edgeWithin, Finset.mem_filter]
  constructor
  · intro he
    exact ⟨⟨he.1, fun v hv => hAS (he.2 v hv)⟩, he.2⟩
  · rintro ⟨⟨h1, -⟩, heA⟩
    exact ⟨h1, heA⟩

/-- **核心分解（`⊆` 方向）**：`F ⊆ E(S)`、`A := reachSet F S m`、`m ∈ S` ⇒
`F ⊆ E(A) ∪ E(S∖A)`。

关键：没有边跨过 `A` 与 `S∖A`。若 `e = s(v,w) ∈ F` 且 `v ∈ A`，则 `v` 与 `m` 可及、
`v` 与 `w` 在 `fromEdgeSet F` 中相邻 ⇒ `w` 与 `m` 可及 ⇒ `w ∈ A`。
这正是蓝图里"`F_B` 不含跨 `A`/`S∖A` 的边"那条事实。 -/
theorem subset_edgeWithin_union_of_reachSet {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S) :
    F ⊆ edgeWithin I (reachSet F S m) ∪ edgeWithin I (S \ reachSet F S m) := by
  intro e he
  revert he
  refine Sym2.ind (fun v w => ?_) e
  intro he
  have hne : ¬ s(v, w).IsDiag := SimpleGraph.not_isDiag_of_mem_edgeFinset
    (Finset.mem_filter.mp (show s(v, w) ∈ I.edgeFinset.filter
      (fun e => ∀ v ∈ e, v ∈ S) from hF he)).1
  have hpair : ∀ x ∈ s(v, w), x ∈ S := mem_of_mem_edgeWithin (hF he)
  have hvS : v ∈ S := hpair v (Sym2.mem_iff.mpr (Or.inl rfl))
  have hwS : w ∈ S := hpair w (Sym2.mem_iff.mpr (Or.inr rfl))
  have hvw : v ≠ w := fun h => hne (Sym2.mk_isDiag_iff.mpr h)
  have hadj : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Adj v w := by
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨he, hvw⟩
  -- 两个端点要么同在 `A` 内，要么同在 `S∖A` 内（可及性把二者绑定）
  have hkey : ∀ (x y : V), y ∈ reachSet F S m →
      (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Adj x y → x ∈ reachSet F S m := by
    intro x y hy hxy
    rw [mem_reachSet] at hy ⊢
    have hrm : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable m x :=
      hy.2.trans (SimpleGraph.Adj.reachable hxy.symm)
    exact ⟨mem_of_reachable_of_subset_edgeWithin hF hm hrm, hrm⟩
  by_cases hvA : v ∈ reachSet F S m
  · have hwA := hkey w v hvA hadj.symm
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (show s(v, w) ∈ I.edgeFinset.filter
          (fun e => ∀ v ∈ e, v ∈ S) from hF he)).1, fun x hx => by
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hvA
        · exact hwA⟩)
  · have hwA : w ∉ reachSet F S m := fun hwA =>
      hvA (hkey v w hwA hadj)
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (show s(v, w) ∈ I.edgeFinset.filter
          (fun e => ∀ v ∈ e, v ∈ S) from hF he)).1, fun x hx => by
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨hvS, hvA⟩
        · exact Finset.mem_sdiff.mpr ⟨hwS, hwA⟩⟩)

/-! ### §15 分量分解的互补半边：`A = reachSet F S m` ⇒ `F ∩ E(A)` **确定** `A` -/

omit [LinearOrder V] in
/-- **走步的每个顶点都在可及集内**：把"与起点可及"翻译成 `reachSet` 的成员资格。 -/
theorem support_subset_reachSet {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S)
    {v : V} (p : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Walk m v) :
    ∀ x ∈ p.support, x ∈ reachSet F S m := by
  intro x hx
  rw [mem_reachSet]
  exact ⟨mem_of_reachable_of_subset_edgeWithin hF hm (reachable_of_mem_support p hx),
    reachable_of_mem_support p hx⟩

omit [LinearOrder V] in
/-- **走步的每条边都落在可及集内**：边的两个端点都在支撑上，而支撑 ⊆ 可及集。 -/
theorem walk_edges_subset_reachSet {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S)
    {v : V} (p : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Walk m v) {e : Sym2 V}
    (he : e ∈ p.edges) : ∀ x ∈ e, x ∈ reachSet F S m := by
  intro x hx
  exact support_subset_reachSet hF hm p x
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hx⟩))

/-- **单射性的核心**：`A = reachSet F S m` 时，`F` 下 `A` 内可及的顶点集
恰由 `F ∩ E(A)` 决定 —— 也就是 `reachSet (F ∩ edgeWithin I A) S m = A`。

左包含：`F ∩ E(A)` 的边都在 `A` 内（`mem_of_mem_edgeWithin` 口径），故可及集 ⊆ `A`。
右包含：`x ∈ A` 给出 `F` 里的一条走步 `m → x`，其每条边都由
`walk_edges_subset_reachSet` 落在 `A` 内，于是这条走步**也是** `F ∩ E(A)` 的走步。 -/
theorem reachSet_inter_edgeWithin_eq {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S A : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S)
    (hA : A = reachSet F S m) :
    reachSet (F ∩ edgeWithin I A) S m = A := by
  subst hA
  refine Finset.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_reachSet] at hx
    exact mem_of_reachable_of_subset_edgeWithin
      (F := F ∩ edgeWithin I (reachSet F S m)) (S := reachSet F S m)
      (fun e he => (Finset.mem_inter.mp he).2)
      (self_mem_reachSet hm) hx.2
  · intro x hx
    rw [mem_reachSet]
    refine ⟨reachSet_subset hx, ?_⟩
    obtain ⟨hxS, hxr⟩ := mem_reachSet.mp hx
    obtain ⟨p⟩ := hxr
    -- 这条走步的边都在 `F` 内、且两端点都在 `A` 内 ⇒ 走步落在 `F ∩ E(A)` 内
    refine ⟨p.transfer (SimpleGraph.fromEdgeSet
      (↑(F ∩ edgeWithin I (reachSet F S m)) : Set (Sym2 V))) (fun e he => ?_)⟩
    -- `e ∈ F`（走步的边落在 `F` 内）
    have heF : e ∈ F := by
      have h := p.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h
      simpa using h.1
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨Finset.mem_inter.mpr ⟨by simpa using heF, ?_⟩, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (show e ∈ I.edgeFinset.filter
            (fun e => ∀ v ∈ e, v ∈ S) from hF heF)).1,
          walk_edges_subset_reachSet hF hm p he⟩
    · exact SimpleGraph.not_isDiag_of_mem_edgeSet
        (G := SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V)))
        (p.edges_subset_edgeSet he)

/-! ### §16 定理 3.2 本体：`connSum` 的续接方程 -/

/-- **分解的唯一性半边**：`F ⊆ E(S)` 时，`F = (F ∩ E(A)) ∪ (F ∩ E(S∖A))`，其中
`A := reachSet F S m`。

（`⊆` 由 `subset_edgeWithin_union_of_reachSet`；反包含由两条 `edgeWithin_mono`。） -/
theorem eq_inter_union_inter_sdiff {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S) :
    F = (F ∩ edgeWithin I (reachSet F S m)) ∪ (F ∩ edgeWithin I (S \ reachSet F S m)) := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    rcases Finset.mem_union.mp (subset_edgeWithin_union_of_reachSet hF hm he) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, h⟩)
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact (Finset.mem_inter.mp h).1
    · exact (Finset.mem_inter.mp h).1

/-- 上面分解中两块的**不交性**：两个顶集不交，故其内部边集不交（`edgeWithin_disjoint`）。 -/
theorem disjoint_inter_of_reachSet {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} {m : V} :
    Disjoint (F ∩ edgeWithin I (reachSet F S m))
      (F ∩ edgeWithin I (S \ reachSet F S m)) :=
  Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right
      (edgeWithin_disjoint (Finset.disjoint_sdiff)))

/-! ### §17 双射：`F ↦ (A_F, F ∩ E(A_F), F ∩ E(S∖A_F))` -/

/-- **`F` 由三分量数据还原**：`A := reachSet F S m` 时
`F = (F ∩ E(A)) ∪ (F ∩ E(S∖A))`（`eq_inter_union_inter_sdiff` 的直接改写）。 -/
theorem eq_union_of_reachSet {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S) :
    F = (F ∩ edgeWithin I (reachSet F S m)) ∪ (F ∩ edgeWithin I (S \ reachSet F S m)) :=
  eq_inter_union_inter_sdiff hF hm

/-- **连通性传递到分量**：`A = reachSet F S m`、`F_A = F ∩ E(A)` ⇒
`((fromEdgeSet F_A).induce A).Connected`（即 `connSum I A` 里的那个条件）。 -/
theorem connected_induce_inter_edgeWithin {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {F : Finset (Sym2 V)} {S : Finset V} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S) :
    ((SimpleGraph.fromEdgeSet (↑(F ∩ edgeWithin I (reachSet F S m)) : Set (Sym2 V))).induce
      (↑(reachSet F S m) : Set V)).Connected := by
  have hkey := connected_induce_reachSet (I := I)
    (F := F ∩ edgeWithin I (reachSet F S m)) (S := S)
    (fun e he => edgeWithin_mono (reachSet_subset (S := S) (m := m))
      (Finset.mem_inter.mp he).2) hm
  have hA : reachSet (F ∩ edgeWithin I (reachSet F S m)) S m = reachSet F S m :=
    reachSet_inter_edgeWithin_eq hF hm rfl
  rw [hA] at hkey
  exact hkey

/-! ### §18 和式重排的记账件 -/

/-- `F_A ⊆ E(A)`、`F_B ⊆ E(S∖A)` ⇒ `F_A ∪ F_B ⊆ E(S)`（当 `A ⊆ S`）。 -/
theorem union_subset_edgeWithin {I : SimpleGraph V} [Fintype ↑I.edgeSet] {A S : Finset V}
    (hAS : A ⊆ S) {FA FB : Finset (Sym2 V)} (hA : FA ⊆ edgeWithin I A)
    (hB : FB ⊆ edgeWithin I (S \ A)) : FA ∪ FB ⊆ edgeWithin I S := by
  refine Finset.union_subset ?_ ?_
  · exact (Finset.Subset.trans hA (edgeWithin_mono hAS))
  · exact (Finset.Subset.trans hB (edgeWithin_mono Finset.sdiff_subset))

/-- **相交还原（左侧）**：`F_A ⊆ E(A)`、`F_B ⊆ E(S∖A)` ⇒ `(F_A ∪ F_B) ∩ E(A) = F_A`。

`⊆`：若 `e ∈ F_B ∩ E(A)`，则 `e` 的两端点既在 `S∖A` 内（`F_B ⊆ E(S∖A)`）
又在 `A` 内（`e ∈ E(A)`）——矛盾。（不需要 `A ⊆ S`，也不需要用不交性。） -/
theorem inter_edgeWithin_eq_left {I : SimpleGraph V} [Fintype ↑I.edgeSet] {A S : Finset V}
    {FA FB : Finset (Sym2 V)} (hA : FA ⊆ edgeWithin I A)
    (hB : FB ⊆ edgeWithin I (S \ A)) :
    (FA ∪ FB) ∩ edgeWithin I A = FA := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨heAB, heEA⟩ := Finset.mem_inter.mp he
    rcases Finset.mem_union.mp heAB with h | h
    · exact h
    · exfalso
      -- `e ∈ F_B ∩ E(A)`：`e` 的任一端点同时属于 `A` 与 `S∖A`
      have heA : e ∈ edgeWithin I A := heEA
      have heB : e ∈ FB := h
      clear heAB heEA h
      revert heA heB
      refine Sym2.ind (fun u v => ?_) e
      intro heA heB
      have huA : u ∈ A := mem_of_mem_edgeWithin heA u (Sym2.mem_iff.mpr (Or.inl rfl))
      have huS : u ∈ S \ A := mem_of_mem_edgeWithin (hB heB) u
        (Sym2.mem_iff.mpr (Or.inl rfl))
      exact (Finset.mem_sdiff.mp huS).2 huA
  · intro e he
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ he, hA he⟩

/-- **相交还原（右侧）**：`F_A ⊆ E(A)`、`F_B ⊆ E(S∖A)` ⇒ `(F_A ∪ F_B) ∩ E(S∖A) = F_B`。
与 `inter_edgeWithin_eq_left` 对称（直接对调两支，不走 `union_comm` 以免 `isDefEq` 超时）。 -/
theorem inter_edgeWithin_eq_right {I : SimpleGraph V} [Fintype ↑I.edgeSet] {A S : Finset V}
    {FA FB : Finset (Sym2 V)} (hA : FA ⊆ edgeWithin I A)
    (hB : FB ⊆ edgeWithin I (S \ A)) :
    (FA ∪ FB) ∩ edgeWithin I (S \ A) = FB := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨heAB, heEB⟩ := Finset.mem_inter.mp he
    rcases Finset.mem_union.mp heAB with h | h
    · exfalso
      have heA : e ∈ edgeWithin I A := hA h
      have heB : e ∈ edgeWithin I (S \ A) := heEB
      clear heAB heEB h hA hB
      revert heA heB
      refine Sym2.ind (fun u v => ?_) e
      intro heA heB
      have huA : u ∈ A := mem_of_mem_edgeWithin heA u (Sym2.mem_iff.mpr (Or.inl rfl))
      have huS : u ∈ S \ A := mem_of_mem_edgeWithin heB u
        (Sym2.mem_iff.mpr (Or.inl rfl))
      exact (Finset.mem_sdiff.mp huS).2 huA
    · exact h
  · intro e he
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ he, hB he⟩

/-! ### §19 定理 3.2 的**和式恒等式**（双射的最终装配） -/

omit [LinearOrder V] in
/-- **`compatInd` 的幂形式和**：`compatInd I T = Σ_{F ⊆ E(T)} (−1)^{|F|}`
（`sum_neg_one_pow_card_edgeWithin` 的重写）。 -/
theorem compatInd_eq_sum_neg_one_pow (I : SimpleGraph V) [Fintype ↑I.edgeSet] (T : Finset V) :
    compatInd I T = ∑ F ∈ (edgeWithin I T).powerset, (-1 : ℤ) ^ F.card :=
  (sum_neg_one_pow_card_edgeWithin T).symm

/-! ### §20 定理 3.2 本体的和式恒等式：双射装配

蓝图 §4.13.1。左边 = `Σ_{F ⊆ E(S)} (−1)^{|F|}`（`compatInd_eq_sum_neg_one_pow`），
右边按 `A = F` 下 `min S` 的连通分量（= `reachSet F S m`）分组。
`§13–§19` 已把分组所需的一切几何事实证完，本节的剩余工作是纯 `Finset` 记账。
-/

/-- **右端的和**（`connSum · compatInd` 的配对展开）：`A` 遍历含 `m` 的 `S` 子集，
`(F_A, F_B)` 遍历 `E(A).powerset × E(S∖A).powerset`，被积项用 `ite` 写（与 `connSum` 同形）。 -/
def pairingSum (I : SimpleGraph V) [Fintype ↑I.edgeSet] (S : Finset V) (m : V) : ℤ :=
  ∑ A ∈ S.powerset.filter (fun A => m ∈ A),
    ∑ FA ∈ (edgeWithin I A).powerset,
      ∑ FB ∈ (edgeWithin I (S \ A)).powerset,
        (if ((SimpleGraph.fromEdgeSet (↑FA : Set (Sym2 V))).induce (↑A : Set V)).Connected
            then (1 : ℤ) else 0) * (-1 : ℤ) ^ (FA ∪ FB).card

/-- **右端和 = `connSum · compatInd`**。

逐个 `A` 化简：`connSum I A · compatInd I (S∖A)`
`= (Σ_{F_A} ite_conn · (−1)^{|F_A|}) · (Σ_{F_B} (−1)^{|F_B|})`
（`compatInd` 的幂形式和），再用 `Finset.sum_mul` / `Finset.mul_sum` 展成双和；
双和的项由 `(-1)^{|F_A|}·(-1)^{|F_B|} = (-1)^{|F_A ∪ F_B|}`（`neg_one_pow_card_union`）对齐。 -/
theorem pairingSum_eq_sum_connSum_mul {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} (hS : S.Nonempty) :
    pairingSum I S (S.min' hS) =
      ∑ A ∈ S.powerset.filter (fun A => S.min' hS ∈ A),
        connSum I A * compatInd I (S \ A) := by
  rw [pairingSum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [connSum, compatInd_eq_sum_neg_one_pow I (S \ A)]
  -- 把右端的乘积展成双和，再与 `pairingSum` 的内层逐项对齐
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun FA _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun FB hFB => ?_
  have hFB' : FB ⊆ edgeWithin I (S \ A) := Finset.mem_powerset.mp hFB
  have hFA' : FA ⊆ edgeWithin I A := by
    have : FA ∈ (edgeWithin I A).powerset := by assumption
    exact Finset.mem_powerset.mp this
  have hd : Disjoint FA FB :=
    Finset.disjoint_of_subset_left hFA'
      (Finset.disjoint_of_subset_right hFB' (edgeWithin_disjoint Finset.disjoint_sdiff))
  rw [Finset.card_union_of_disjoint hd, pow_add]
  by_cases hc : ((SimpleGraph.fromEdgeSet (↑FA : Set (Sym2 V))).induce
      (↑A : Set V)).Connected <;> simp [hc]

/-! ### §21 双射：`F ↦ (reachSet F S m, F ∩ E(A), F ∩ E(S∖A))` -/

/-- **正向映射的三元组**（打成待配对的形式）。 -/
def toComponents (I : SimpleGraph V) [Fintype ↑I.edgeSet] (S : Finset V) (m : V)
    (F : Finset (Sym2 V)) : Finset V × Finset (Sym2 V) × Finset (Sym2 V) :=
  (reachSet F S m, F ∩ edgeWithin I (reachSet F S m),
    F ∩ edgeWithin I (S \ reachSet F S m))

/-- **反向映射**：把三分量数据合回 `F_A ∪ F_B`。 -/
def ofComponents (p : Finset V × Finset (Sym2 V) × Finset (Sym2 V)) : Finset (Sym2 V) :=
  p.2.1 ∪ p.2.2

/-- **左逆**：`F ⊆ E(S)` ⇒ `ofComponents (toComponents F) = F`。 -/
theorem ofComponents_toComponents {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    {F : Finset (Sym2 V)} (hF : F ⊆ edgeWithin I S) {m : V} (hm : m ∈ S) :
    ofComponents (toComponents I S m F) = F := by
  rw [ofComponents, toComponents]
  exact (eq_inter_union_inter_sdiff hF hm).symm

/-- **`FA ∪ FB` 的边都落在 `A ∪ (S∖A)`**，且没有跨边：`FA` 的边在 `A` 内、
`FB` 的边在 `S∖A` 内。（这是"分量不跨"的另一面。） -/
theorem mem_of_mem_union_edges {I : SimpleGraph V} [Fintype ↑I.edgeSet] {A S : Finset V}
    {FA FB : Finset (Sym2 V)} (hFA : FA ⊆ edgeWithin I A)
    (hFB : FB ⊆ edgeWithin I (S \ A)) {e : Sym2 V} (he : e ∈ FA ∪ FB) :
    (∀ v ∈ e, v ∈ A) ∨ (∀ v ∈ e, v ∈ S \ A) := by
  rcases Finset.mem_union.mp he with h | h
  · exact Or.inl (mem_of_mem_edgeWithin (hFA h))
  · exact Or.inr (mem_of_mem_edgeWithin (hFB h))

/-- **走步不跨分量**：`FA` 的边全在 `A` 内、`FB` 的边全在 `S∖A` 内，
且走步起点在 `A` 内 ⇒ 走步的**每个顶点**都在 `A` 内。

关键：每条边要么整个在 `A` 内、要么整个在 `S∖A` 内，故从 `A` 内出发永远跨不出去。 -/
theorem walk_support_subset_of_components {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S A : Finset V} {FA FB : Finset (Sym2 V)} (hFA : FA ⊆ edgeWithin I A)
    (hFB : FB ⊆ edgeWithin I (S \ A)) :
    ∀ {m x : V}, m ∈ A →
      (p : (SimpleGraph.fromEdgeSet (↑(FA ∪ FB) : Set (Sym2 V))).Walk m x) →
      ∀ y ∈ p.support, y ∈ A := by
  intro m x hm p
  induction p with
  | nil =>
    intro y hy
    rw [SimpleGraph.Walk.support_nil] at hy
    rw [List.mem_singleton] at hy
    subst hy
    exact hm
  | @cons u v w hadj tail ih =>
    intro y hy
    rw [SimpleGraph.Walk.support_cons] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hm
    · -- 边 `s(u,v)` 只能整个在 `A` 内（因为 `u ∈ A`）⇒ `v ∈ A`，再对尾走步用归纳假设
      have hmem : (s(u, v) : Sym2 V) ∈ FA ∪ FB := by
        rw [SimpleGraph.fromEdgeSet_adj] at hadj
        exact hadj.1
      have hv : v ∈ A := by
        rcases mem_of_mem_union_edges hFA hFB hmem with h | h
        · exact h v (Sym2.mem_iff.mpr (Or.inr rfl))
        · exact absurd hm (Finset.mem_sdiff.mp
            (h u (Sym2.mem_iff.mpr (Or.inl rfl)))).2
      exact ih hv y hy

/-- **右逆（第一分量）**：三分量数据合法时，由它合成的 `F_A ∪ F_B` 在 `m` 处的可及集
恰回到 `A`。

`⊆`：`FA ∪ FB` 的每条边要么整个在 `A` 内、要么整个在 `S∖A` 内（无跨边），
而走步从 `m ∈ A` 出发 ⇒ 走步离不开 `A`（`walk_support_subset_of_components`）。
`⊇`：`FA` 在 `A` 上连通生成 ⇒ `A` 的每点都与 `m` 在 `FA` 内可及。 -/
theorem reachSet_ofComponents {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    {A : Finset V} {FA FB : Finset (Sym2 V)} {m : V} (hAS : A ⊆ S) (hm : m ∈ A)
    (hFA : FA ⊆ edgeWithin I A) (hFB : FB ⊆ edgeWithin I (S \ A))
    (hconn : ((SimpleGraph.fromEdgeSet (↑FA : Set (Sym2 V))).induce
      (↑A : Set V)).Connected) :
    reachSet (FA ∪ FB) S m = A := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨-, hxr⟩ := mem_reachSet.mp hx
    obtain ⟨p⟩ := hxr
    exact walk_support_subset_of_components hFA hFB hm p x
      (SimpleGraph.Walk.end_mem_support p)
  · intro x hx
    rw [mem_reachSet]
    refine ⟨hAS hx, ?_⟩
    -- `FA` 在 `A` 上连通 ⇒ `m` 与 `x` 在 `induce A` 内可及 ⇒ 在 `FA ∪ FB` 内可及
    have hreach := hconn ⟨m, hm⟩ ⟨x, hx⟩
    obtain ⟨q⟩ := hreach
    -- 把 `induce A` 的走步映回 `FA`，再沿 `FA ≤ FA ∪ FB` 放大
    refine ⟨(q.map (SimpleGraph.Embedding.induce _).toHom).mapLe
      (SimpleGraph.fromEdgeSet_mono (by
        rw [Finset.coe_union]
        exact Set.subset_union_left)) |>.copy rfl rfl⟩

/-! ### §22 双射的最终装配：`Σ_{F ⊆ E(S)} (−1)^{|F|} = pairingSum I S m`

本节的记账只用 `Finset.sum_biUnion`。**本版 Mathlib 没有 `Finset.sum_product` /
`Finset.sum_sigma`**（实测 `#check` 确认 unknown identifier），故下面先补一条
`sum_product` 的局部版本（对第二个因子归纳）。 -/

omit [LinearOrder V] in
/-- **乘积上的求和分解**（本版 Mathlib 缺失的 `Finset.sum_product`）：
`∑_{p ∈ s ×ˢ t} f p = ∑_{a ∈ s} ∑_{b ∈ t} f (a, b)`。

用 `Finset.product_eq_biUnion` 把 `×ˢ` 写成 `biUnion`，再套 `sum_biUnion`。 -/
theorem sum_product' {α β M : Type*} [DecidableEq α] [DecidableEq β] [AddCommMonoid M]
    (s : Finset α) (t : Finset β) (f : α × β → M) :
    ∑ p ∈ s ×ˢ t, f p = ∑ a ∈ s, ∑ b ∈ t, f (a, b) := by
  have : DecidableEq (α × β) := inferInstance
  rw [Finset.product_eq_biUnion, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_image]
    intro b _ b' _ h
    exact (Prod.ext_iff.mp h).2
  · -- 各 `a`-纤维（竖列）互不相交
    intro a _ a' _ hne
    exact Finset.disjoint_left.mpr fun p hp hp' => by
      rw [Finset.mem_image] at hp hp'
      obtain ⟨b, _, hb⟩ := hp
      obtain ⟨b', _, hb'⟩ := hp'
      -- `hb : (a, b) = p`、`hb' : (a', b') = p`
      exact hne (Prod.ext_iff.mp (hb.trans hb'.symm)).1

/-! ### §23 扁平索引集 `compIndex` 与配对和的桥接 -/

/-- **分量数据的扁平索引集**：`(A, (F_A, F_B))`，其中 `A` 遍历含 `m` 的 `S` 子集、
`F_A ⊆ E(A)` 且 **`F_A` 在 `A` 上连通生成**、`F_B ⊆ E(S∖A)`。

连通性过滤**内建**在索引集里（蓝图 §4.13.1 的"连通生成子图"），
这样 `sum_bij'` 的双射才是**精确**的（否则索引集比像大，右逆不成立）。
纤维用 `{A} ×ˢ …` 钉住第一个分量，成员关系能反解出 `A`。 -/
def compIndex (I : SimpleGraph V) [Fintype ↑I.edgeSet] (S : Finset V) (m : V) :
    Finset (Finset V × (Finset (Sym2 V) × Finset (Sym2 V))) :=
  (S.powerset.filter (fun A => m ∈ A)).biUnion fun A =>
    ({A} : Finset (Finset V)) ×ˢ
      (((edgeWithin I A).powerset.filter (fun FA : Finset (Sym2 V) =>
          ((SimpleGraph.fromEdgeSet (FA : Set (Sym2 V))).induce
            (A : Set V)).Connected)) ×ˢ (edgeWithin I (S \ A)).powerset)

/-- **配对和用 `compIndex` 重写**（`sum_biUnion` + `sum_product'`）。

索引集里 `F_A` 已按连通性过滤，故被积项的连通性因子恒为 `1`。 -/
theorem pairingSum_eq_sum_compIndex {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    (S : Finset V) (m : V) :
    pairingSum I S m = ∑ p ∈ compIndex I S m, (-1 : ℤ) ^ (p.2.1 ∪ p.2.2).card := by
  rw [pairingSum, compIndex, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun A _ => ?_
    -- 先把 `{A} ×ˢ (P' ×ˢ Q)` 上的和展成 `∑_{FA} ∑_{FB}`，其中 `P'` 带连通性过滤
    rw [sum_product', Finset.sum_singleton, sum_product']
    -- 左端（`pairingSum`）的内层：`(if conn then 1 else 0) * (−1)^{|FA ∪ FB|}`
    -- 右端（`compIndex`）的内层：`∑_{FA ∈ P'} ∑_{FB} (−1)^{|FA ∪ FB|}`
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun FA _ => ?_
    by_cases hc : ((SimpleGraph.fromEdgeSet (↑FA : Set (Sym2 V))).induce
        (↑A : Set V)).Connected
    · simp only [hc, ite_true, one_mul]
    · simp only [hc, ite_false, zero_mul, Finset.sum_const_zero]
  · -- 不同 `A` 的纤维不相交（第一个分量分别被钉在 `A`、`A'` 上）
    intro A _ A' _ hne
    exact Finset.disjoint_left.mpr fun p hp hp' => by
      rw [Finset.mem_product, Finset.mem_product] at hp hp'
      exact hne ((Finset.mem_singleton.mp hp.1).symm.trans (Finset.mem_singleton.mp hp'.1))

/-- **`compIndex` 的成员刻画**：由第一个分量**反解出** `A`。 -/
theorem mem_compIndex {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V} {m : V}
    {A : Finset V} {FA FB : Finset (Sym2 V)} :
    (A, (FA, FB)) ∈ compIndex I S m ↔ A ⊆ S ∧ m ∈ A ∧ FA ⊆ edgeWithin I A ∧
      ((SimpleGraph.fromEdgeSet (↑FA : Set (Sym2 V))).induce (↑A : Set V)).Connected ∧
      FB ⊆ edgeWithin I (S \ A) := by
  rw [compIndex, Finset.mem_biUnion]
  constructor
  · rintro ⟨A', hA', hmem⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hmem hA'
    obtain rfl : A = A' := Finset.mem_singleton.mp hmem.1
    exact ⟨hA'.1, hA'.2, hmem.2.1.1, hmem.2.1.2, hmem.2.2⟩
  · rintro ⟨hAS, hmA, hFA, hconn, hFB⟩
    refine ⟨A, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hAS, hmA⟩
    · refine Finset.mem_product.mpr ⟨Finset.mem_singleton_self A, ?_⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hFA, hconn⟩, Finset.mem_powerset.mpr hFB⟩

/-! ### §24 双射装配：`Σ_{F ⊆ E(S)} (−1)^{|F|} = pairingSum I S m` -/

/-- **定理 3.2 的和式恒等式**（双射 `F ↦ (reachSet F S m, F∩E(A), F∩E(S∖A))`）。

`sum_bij'` 的两个回代分别是 `ofComponents_toComponents`（左逆）与
`reachSet_ofComponents` + `inter_edgeWithin_eq_left`（右逆）。
被积项的对齐用 `F ∩ E(A) ∪ F ∩ E(S∖A) = F`（`eq_inter_union_inter_sdiff`）与
`connSum` 的连通性条件（`connected_induce_inter_edgeWithin`）。 -/
theorem sum_neg_one_pow_eq_pairingSum {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} (hS : S.Nonempty) :
    (∑ F ∈ (edgeWithin I S).powerset, (-1 : ℤ) ^ F.card) = pairingSum I S (S.min' hS) := by
  rw [pairingSum_eq_sum_compIndex]
  refine Finset.sum_bij'
    (fun F _ => (reachSet F S (S.min' hS),
      (F ∩ edgeWithin I (reachSet F S (S.min' hS)),
       F ∩ edgeWithin I (S \ reachSet F S (S.min' hS)))))
    (fun p _ => p.2.1 ∪ p.2.2) ?_ ?_ ?_ ?_ ?_
  · -- `i` 落在 `compIndex` 里
    intro F hF
    rw [mem_compIndex]
    have hsub : F ⊆ edgeWithin I S := Finset.mem_powerset.mp hF
    have hm : S.min' hS ∈ S := Finset.min'_mem S hS
    exact ⟨reachSet_subset, self_mem_reachSet hm, Finset.inter_subset_right,
      connected_induce_inter_edgeWithin hsub hm, Finset.inter_subset_right⟩
  · -- `j` 落在 `(edgeWithin I S).powerset` 里
    intro p hp
    rw [mem_compIndex] at hp
    obtain ⟨hAS, hmA, hFA, -, hFB⟩ := hp
    rw [Finset.mem_powerset]
    exact union_subset_edgeWithin hAS hFA hFB
  · -- 左逆：`j (i F) = F`
    intro F hF
    have hsub : F ⊆ edgeWithin I S := Finset.mem_powerset.mp hF
    exact ofComponents_toComponents hsub (Finset.min'_mem S hS)
  · -- 右逆：`i (j p) = p`
    intro p hp
    rw [mem_compIndex] at hp
    obtain ⟨hAS, hmA, hFA, hconn, hFB⟩ := hp
    have hreach := reachSet_ofComponents hAS hmA hFA hFB hconn
    -- `p = (A, (FA, FB))`；把 `reachSet (FA ∪ FB) S m` 换成 `A` 后逐一对照
    obtain ⟨A, ⟨FA, FB⟩⟩ := p
    simp only at hreach ⊢
    rw [hreach, inter_edgeWithin_eq_left hFA hFB, inter_edgeWithin_eq_right hFA hFB]
  · -- 被积项对齐：`F = F_A ∪ F_B` ⇒ 指数对齐
    intro F hF
    have hsub : F ⊆ edgeWithin I S := Finset.mem_powerset.mp hF
    rw [← eq_inter_union_inter_sdiff hsub (Finset.min'_mem S hS)]

/-! ### §25 定理 3.2：`connSum` 的续接方程 -/

/-- **定理 3.2 的续接方程**（一般情形，`S` 不必相容）：

> `compatInd I S = Σ_{A ∈ S.powerset.filter (min S ∈ ·)} connSum I A * compatInd I (S∖A)`

由左侧恒等式（`compatInd` = `Σ_{F ⊆ E(S)} (−1)^{|F|}`）、双射
（`sum_neg_one_pow_eq_pairingSum`）与右端配对展开
（`pairingSum_eq_sum_connSum_mul`）三者串联得到。 -/
theorem compatInd_eq_sum_connSum {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} (hS : S.Nonempty) :
    compatInd I S = ∑ A ∈ S.powerset.filter (fun A => S.min' hS ∈ A),
      connSum I A * compatInd I (S \ A) := by
  rw [compatInd_eq_sum_neg_one_pow I S, sum_neg_one_pow_eq_pairingSum hS,
    pairingSum_eq_sum_connSum_mul hS]

/-! ### §26 收口：`ursell = connSum` 与引理 3.1 的另一半 -/

/-- **`ursell = connSum`**（定理 3.2 本体）。

两者满足**同一条续接方程**（`ursell` 侧 = `compatInd_eq_sum`、`connSum` 侧 =
`compatInd_eq_sum_connSum`），对 `S.card` 强归纳即得。

由 `IsCompatible I S ↔ edgeWithin I S = ∅` 可知"相容情形"两侧同为 0/1，
归纳步则把 `S` 的真子集上的相等性逐项搬运。 -/
theorem ursell_eq_connSum (I : SimpleGraph V) [Fintype ↑I.edgeSet] :
    ∀ S : Finset V, ursell I S = connSum I S := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S.Nonempty
    · -- 两侧的续接方程：`ursell` 版（`compatInd_eq_sum`）与 `connSum` 版
      -- （`compatInd_eq_sum_connSum`）。把两者都拆到"非 `S` 部分"，再用归纳假设逐项对齐。
      have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
      -- `ursell` 侧的续接方程
      have hurs := ursell_eq_of_nonempty I hS
      -- `connSum` 侧的续接方程
      have hconn := compatInd_eq_sum_connSum (I := I) hS
      -- 把 `connSum` 侧的和拆出 `A = S` 项
      have hself : connSum I S * compatInd I (S \ S) = connSum I S := by
        rw [Finset.sdiff_self, compatInd_empty, mul_one]
      have hmemS : S ∈ S.powerset.filter (fun T => S.min' hS ∈ T) :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl S), hmin⟩
      have hsplit := Finset.sum_erase_add
        (s := S.powerset.filter (fun T => S.min' hS ∈ T))
        (f := fun A => connSum I A * compatInd I (S \ A)) hmemS
      -- `ursell` 侧的 filter 恰是"去掉 `S`"后的集合
      have hfil : S.powerset.filter (fun T => S.min' hS ∈ T ∧ T ≠ S)
          = (S.powerset.filter (fun T => S.min' hS ∈ T)).erase S := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
        tauto
      -- "非 `S` 部分"逐项相等（对 `A ⊊ S` 用归纳假设）
      have hpair : ∑ A ∈ (S.powerset.filter (fun T => S.min' hS ∈ T)).erase S,
            ursell I A * compatInd I (S \ A)
          = ∑ A ∈ (S.powerset.filter (fun T => S.min' hS ∈ T)).erase S,
            connSum I A * compatInd I (S \ A) := by
        refine Finset.sum_congr rfl fun A hA => ?_
        rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hA
        rw [ih A (lt_of_le_of_ne hA.2.1 hA.1)]
      rw [hurs, hfil, hpair]
      linarith [hconn, hsplit, hself]
    · -- `S = ∅`：`ursell I ∅ = 0 = connSum I ∅`
      rw [Finset.not_nonempty_iff_eq_empty.mp hS, connSum_empty, ursell_empty]

/-! ### §27 引理 3.1 的另一半：连通 ⇒ `φ ≠ 0`

**归约**：由 `ursell_eq_connSum` 只须证纯图论命题"连通图的连通生成子图交错和非零"。

**路线（边数比较，已跑通）**：设 `S` 上的诱导图 `I.induce S` 是树。对任意
`F ⊆ E(S)` 令 `G_F := (fromEdgeSet F).induce S`、`G_E := I.induce S`；两者**顶点类型相同**
（都是 `↥S`）且 `G_F ≤ G_E`。
- `G_E.IsTree` ⇒ `G_E.edgeFinset.card + 1 = S.card`（`IsTree.card_edgeFinset`）；
- `G_F.Connected` ⇒ 含生成树（`Connected.exists_isTree_le`）⇒ `G_F.edgeFinset.card + 1 ≥ S.card`。

故 `G_F.edgeFinset = G_E.edgeFinset`，再由 `F ⊆ E(S)` 的逐边描述得 `F = E(S)`。
于是 `connSum I S` 只剩 `F = E(S)` 一项：`connSum I S = (−1)^{|S|−1} ≠ 0`。 -/

/-- **`connSum` 的非零性判据（单顶点）**：`connSum I {m} = 1 ≠ 0`。 -/
theorem connSum_singleton_ne_zero {I : SimpleGraph V} [Fintype ↑I.edgeSet] (m : V) :
    connSum I ({m} : Finset V) ≠ 0 := by
  rw [connSum_singleton]
  norm_num

omit [LinearOrder V] in
/-- `F ⊆ E(S)` ⇒ `G_F ≤ G_E`（同顶点类型的两个诱导图）。 -/
theorem induce_le_of_subset_edgeWithin {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} (hF : F ⊆ edgeWithin I S) :
    (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V) ≤ I.induce (↑S : Set V) := by
  intro u v huv
  rw [SimpleGraph.induce_adj] at huv ⊢
  -- `F` 的边都在 `E(S)` 内 ⇒ 每条也是 `I` 的边
  have hmem : (s(u, v) : Sym2 V) ∈ F := by
    rw [SimpleGraph.fromEdgeSet_adj] at huv
    exact huv.1
  have hE := hF hmem
  rw [edgeWithin, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet] at hE
  exact hE.1

omit [LinearOrder V] in
/-- **树上只有自身这一个连通生成子图**（边数比较，见 §27 路线）。 -/
theorem eq_edgeWithin_of_connected_of_isTree {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} (htree : (I.induce (↑S : Set V)).IsTree) {F : Finset (Sym2 V)}
    (hF : F ⊆ edgeWithin I S)
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    F = edgeWithin I S := by
  have hle := induce_le_of_subset_edgeWithin hF
  -- 边集的包含关系与基数（用 `edgeFinset_mono`，避免逐边 `mem_edgeSet` 的 `Sym2` 记账）
  have hsub := SimpleGraph.edgeFinset_mono hle
  -- `G_E` 是树 ⇒ 边数 = `|S| − 1`
  have hEcard : (I.induce (↑S : Set V)).edgeFinset.card = S.card - 1 := by
    have h := htree.card_edgeFinset
    have hc : Fintype.card (↥(S : Set V)) = S.card := by simp
    omega
  -- `G_F` 连通 ⇒ 含生成树 ⇒ 边数 ≥ `|S| − 1`
  have hFcard : S.card - 1 ≤ ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce
        (↑S : Set V)).edgeFinset.card := by
    obtain ⟨T, hTle, hTtree⟩ := hconn.exists_isTree_le
    have h1 := hTtree.card_edgeFinset
    have hc : Fintype.card (↥(S : Set V)) = S.card := by simp
    have h2 : T.edgeFinset.card ≤ ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce
        (↑S : Set V)).edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hTle)
    omega
  -- 两者边数相同 ⇒ 边集相同
  have hedgeEq : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce
        (↑S : Set V)).edgeFinset = (I.induce (↑S : Set V)).edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  -- 由边数相同推出 `F = E(S)`：改用**顶点级**的邻接外延，绕开 `induce` 的 `Sym2` 强转。
  --
  -- 关键观察：对 `u, v ∈ S`，`s(u,v) ∈ E(S) ↔ I.Adj u v`，
  -- 而 `I.Adj u v ↔ (I.induce S).Adj ⟨u,_⟩ ⟨v,_⟩`（`induce_adj`）。
  -- 边数相同说明 `G_F` 与 `G_E` 的边集相同，于是 `I.Adj u v → G_F.Adj ⟨u,_⟩ ⟨v,_⟩ → s(u,v) ∈ F`。
  refine Finset.Subset.antisymm hF ?_
  intro e he
  -- 用 `Sym2.ind` 把目标换成 `s(u,v)` 形式；`he` 先收进 `have` 以免被 `ind` 一般化
  have hkey : ∀ u v : V, (s(u, v) : Sym2 V) ∈ edgeWithin I S → (s(u, v) : Sym2 V) ∈ F := by
    intro u v huv
    have huS : u ∈ S := mem_of_mem_edgeWithin huv u (Sym2.mem_iff.mpr (Or.inl rfl))
    have hvS : v ∈ S := mem_of_mem_edgeWithin huv v (Sym2.mem_iff.mpr (Or.inr rfl))
    -- 在 `↥S` 上做邻接论证
    have hadjE : (I.induce (↑S : Set V)).Adj ⟨u, huS⟩ ⟨v, hvS⟩ := by
      rw [SimpleGraph.induce_adj]
      have h1 : (s(u, v) : Sym2 V) ∈ I.edgeSet := by
        rw [← SimpleGraph.mem_edgeFinset]
        exact (Finset.mem_filter.mp (show (s(u, v) : Sym2 V) ∈ I.edgeFinset.filter
          (fun e => ∀ x ∈ e, x ∈ S) from huv)).1
      rwa [SimpleGraph.mem_edgeSet] at h1
    have hmemE : (s(⟨u, huS⟩, ⟨v, hvS⟩) : Sym2 (↥(S : Set V))) ∈
        (I.induce (↑S : Set V)).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadjE
    have hmemF : (s(⟨u, huS⟩, ⟨v, hvS⟩) : Sym2 (↥(S : Set V))) ∈
        ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).edgeFinset := by
      rw [hedgeEq]; exact hmemE
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj,
      SimpleGraph.fromEdgeSet_adj] at hmemF
    simpa using hmemF.1
  revert he
  refine Sym2.ind (fun u v => ?_) e
  intro he
  exact hkey u v he

/-- **树上的 `connSum`**：`I.induce S` 是树 ⇒ `connSum I S = (−1)^{|E(S)|}`。

由 `eq_edgeWithin_of_connected_of_isTree`：`F = E(S)` 是唯一的连通生成子图
（`E(S)` 自己显然连通生成，故求和只剩这一项）。 -/
theorem connSum_eq_neg_one_pow_of_isTree {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} (htree : (I.induce (↑S : Set V)).IsTree) :
    connSum I S = (-1 : ℤ) ^ ((edgeWithin I S).card) := by
  rw [connSum]
  -- `E(S)` 诱导的图就是 `I.induce S` 的边集，故连通；其余项由 `eq_edgeWithin_of_connected_of_isTree` 排除
  rw [Finset.sum_eq_single (edgeWithin I S)]
  · -- `F = E(S)` 项：连通性条件成立。
    -- `G_{E(S)} := (fromEdgeSet E(S)).induce S` 与 `G_E := I.induce S` **相等**
    -- （同顶点类型、同边集：`u,v ∈ S` 时 `I.Adj u v ↔ s(u,v) ∈ E(S)`），
    -- 故 `G_{E(S)}.Connected` 由 `htree.isConnected` 平移得到。
    refine ite_eq_left ?_
    have hEq : (SimpleGraph.fromEdgeSet (↑(edgeWithin I S) : Set (Sym2 V))).induce
        (↑S : Set V) = I.induce (↑S : Set V) := by
      refine le_antisymm (induce_le_of_subset_edgeWithin (Finset.Subset.refl _)) ?_
      intro u v huv
      rw [SimpleGraph.induce_adj] at huv ⊢
      -- `u,v ∈ S` 且 `I.Adj ↑u ↑v` ⇒ `s(↑u,↑v) ∈ E(S)`
      have hmem : (s(↑u, ↑v) : Sym2 V) ∈ edgeWithin I S := by
        rw [edgeWithin, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact ⟨huv, fun x hx => by
          rcases Sym2.mem_iff.mp hx with rfl | rfl
          · exact u.2
          · exact v.2⟩
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨hmem, fun h => SimpleGraph.irrefl I (h ▸ huv)⟩
    rw [hEq]
    exact htree.connected
  · -- 其余 `F ⊊ E(S)` 不连通 ⇒ 项为 0
    intro F hF hne
    refine ite_eq_right fun hconn => ?_
    exact hne (eq_edgeWithin_of_connected_of_isTree htree
      (Finset.mem_powerset.mp hF) hconn)
  · -- `E(S) ∈ E(S).powerset`
    intro h
    exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

/-! #### 引理 3.1 另一半：**已证部分**与**剩余部分的精确形态**

**已证**（本文件内）：
* `connSum_eq_neg_one_pow_of_isTree` —— `I.induce S` 是**树** ⇒ `connSum I S = (−1)^{|E(S)|} ≠ 0`；
* `connSum_singleton_ne_zero` —— 单点。

**剩余**：一般**连通**（非树）的 `S` 上 `connSum I S ≠ 0`。

**⚠️ 一条必须记住的更正**（否则会重推错）：一般连通图上
`connSum I S` **不等于** `(−1)^{|S|−1}`，也**不等于** `(−1)^{|S|−1}·τ(S)`（生成树个数）。
实测（穷举所有连通生成子图的交错和）：

| 图 | connSum |
|---|---|
| 树 `P3`（3 点） | `1` |
| 三角形 `K3` | `2` |
| 4-圈 `C4` | `−3` |
| `K4 − e` | `−4` |
| `K4` | `−6` |

（`K3` 的生成树数是 3，而 `connSum = 2` —— 两个"显然的"闭式都是错的。）
正确的对象是**键格（bond lattice）的 Möbius 函数**取值，这正是它一般 `≠ 0` 的原因。

**正确的归纳引擎**（实测验证，见下）：对**非割边** `e`
`connSum I S = connSum(G − e) − connSum(G/e)`（删–缩）。
`K4` 实测：`connSum(K4−e) = −4`、`connSum(K4/e) = 2`、`−4 − 2 = −6 = connSum(K4)` ✔。

**卡在哪**：本版 Mathlib **没有图收缩**（`#check SimpleGraph.contract` / `quotient`
均 unknown identifier；只有 `IsBridge` 与 `deleteEdges`）。
故"删–缩"路线需要自建收缩（顶点合并 + 边集搬运），或改走
**NBC 集 / Tutte 多项式**那条等价路线 —— 都是**独立于续接方程的第二块组合学开发**。

**非零性本身已独立确认**（穷举，非证明）：271 个随机连通图（n = 3..6，边数 n−1..n+2）
的 `connSum` **无一个为零**。 -/

omit [LinearOrder V] in
/-- **配对消去（不含连通性约束的版本）**：把 `E` 的所有子集按是否含 `e` 分成两类，
两类的交错和互为相反数（因为 `E` 非空时全和为 0）。 -/
theorem sum_with_edge_eq_neg_sum_without {α : Type*} [DecidableEq α] {E : Finset α}
    {e : α} (he : e ∈ E) :
    (∑ F ∈ E.powerset.filter (fun F => e ∈ F), (-1 : ℤ) ^ F.card)
      = -(∑ F ∈ E.powerset.filter (fun F => e ∉ F), (-1 : ℤ) ^ F.card) := by
  -- 两类互补；两者之和 = `E.powerset` 上的全和
  have hsplit : (∑ F ∈ E.powerset.filter (fun F => e ∈ F), (-1 : ℤ) ^ F.card)
      + (∑ F ∈ E.powerset.filter (fun F => e ∉ F), (-1 : ℤ) ^ F.card)
      = ∑ F ∈ E.powerset, (-1 : ℤ) ^ F.card := by
    rw [← Finset.sum_filter_add_sum_filter_not E.powerset (fun F => e ∈ F)]
  -- 全和 = 0（`E` 非空时 `Σ_{F ⊆ E} (−1)^{|F|} = [E = ∅] = 0`）
  have hzero : (∑ F ∈ E.powerset, (-1 : ℤ) ^ F.card) = 0 := by
    rw [sum_powerset_neg_one_pow_card]
    exact ite_eq_right (Finset.nonempty_iff_ne_empty.mp ⟨e, he⟩)
  linarith

/-! ##### 符号反转对合（免收缩的核心引理）

**命题**：设 `S` 上的边集 `E`、`e ∈ E`。在"`e` 不是 `F` 的割边"这一范围内，
映射 `F ↦ F ∆ {e}` 是**无不动点的对合**，且 `|F ∆ {e}| = |F| ± 1`（符号相反）。
故这些项两两相消，`connSum I S` 只剩"`e` 是 `F` 的割边"的那些 `F`。

**割边的免收缩刻画**：`e = s(a,b)` 是 `F` 的割边 ⟺ 在 `F ∖ {e}` 里 `a` 与 `b` 不可达
（`SimpleGraph.IsBridge` 的 `isBridge_iff` 就是这个意思）。 -/

omit [LinearOrder V] in
/-- **删一条非割边不改变可及关系**：若 `e` 不是 `G` 的割边，
则 `G.deleteEdges {e}` 与 `G` 有**相同**的可及关系。

证明：`G.deleteEdges {e} ≤ G` 给出一个方向；反向用 `Walk.toDeleteEdges` ——
一条经过 `e` 的走步可以把每一步 `e` 用 `¬IsBridge` 提供的替代走步替换掉
（`IsBridge` 的定义就是"删掉后两端仍可达"）。 -/
theorem reachable_deleteEdges_iff {G : SimpleGraph V} {e : Sym2 V}
    (hnb : ¬ G.IsBridge e) {u v : V} :
    (G.deleteEdges {e}).Reachable u v ↔ G.Reachable u v := by
  constructor
  · intro h
    exact h.mono (by
      intro a b hab
      exact (SimpleGraph.deleteEdges_adj.mp hab).1)
  · intro h
    -- `¬IsBridge e` ⟹ 删边图里 `e` 的两端仍可及
    have hkey : ∀ a b : V, e = s(a, b) → (G.deleteEdges {e}).Reachable a b := by
      intro a b hab
      subst hab
      rw [SimpleGraph.isBridge_iff] at hnb
      simpa using not_not.mp hnb
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    -- 对 `G` 里的 `ReflTransGen` 路径做 tail 归纳，逐步搬入删边图
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hadj ih =>
      rename_i a b _
      by_cases hEq : (s(a, b) : Sym2 V) = e
      · -- 这一步就是 `e`：用 `hkey` 接上
        exact ih.trans ((SimpleGraph.reachable_iff_reflTransGen a b).mp (hkey a b hEq.symm))
      · -- 这一步不是 `e`：可直接搬入
        refine ih.trans ?_
        exact Relation.ReflTransGen.single (by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨hadj, by simpa [Set.mem_singleton] using hEq⟩)

/-- **图恒等式**：`fromEdgeSet F` 删掉边 `e` 就是 `fromEdgeSet (F ∖ {e})`。
（`deleteEdges_fromEdgeSet` + 集合差与 `Finset` 差的对应。） -/
theorem deleteEdges_fromEdgeSet_singleton {F : Finset (Sym2 V)} {e : Sym2 V} :
    (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).deleteEdges {e}
      = SimpleGraph.fromEdgeSet (↑(F \ {e}) : Set (Sym2 V)) := by
  rw [SimpleGraph.deleteEdges_fromEdgeSet]
  congr 1
  ext x
  simp only [Set.mem_sdiff, Finset.mem_coe, Finset.mem_sdiff]
  constructor
  · rintro ⟨hx, hne⟩
    exact ⟨hx, fun h => hne (by simpa using h)⟩
  · rintro ⟨hx, hne⟩
    exact ⟨hx, fun h => hne (by simpa using h)⟩
/-- **对合的另一半**：`F` 连通生成、`e ∈ F`、且 `e` 不是 `F` 的割边 ⇒ `F ∖ {e}` 连通生成。

`¬IsBridge e` 经 `isBridge_iff` 给出"删 `e` 后其两端仍可达"；把那条走步搬到
`fromEdgeSet (F ∖ {e})`（用 `deleteEdges_fromEdgeSet_singleton` 对齐两个图），
于是 `e` 不承担任何必要的连通职责 ⇒ `F∖{e}` 仍连通生成。 -/
theorem connected_spanning_erase_of_not_isBridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {e : Sym2 V} (hF : F ⊆ edgeWithin I S)
    (hnb : ¬ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsBridge e)
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    ((SimpleGraph.fromEdgeSet (↑(F \ {e}) : Set (Sym2 V))).induce (↑S : Set V)).Connected := by
  -- 关键：`fromEdgeSet (F∖{e})` 就是 `(fromEdgeSet F).deleteEdges {e}`
  have hEq : SimpleGraph.fromEdgeSet (↑(F \ {e}) : Set (Sym2 V))
      = (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).deleteEdges {e} :=
    deleteEdges_fromEdgeSet_singleton.symm
  rw [hEq]
  -- 两图在 `S` 上可及关系相同；且 `F` 的走步留在 `S` 内（`F ⊆ E(S)`）
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hconn ⊢
  obtain ⟨w₀, hw₀⟩ := hconn
  refine ⟨w₀, fun w => ?_⟩
  obtain ⟨p⟩ := hw₀ w
  -- 把 `induce S` 的走步映回 `V`，搬进删边图，再 `induce` 回来
  have hV : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable (↑w₀) (↑w) :=
    ⟨p.map (SimpleGraph.Embedding.induce _).toHom⟩
  obtain ⟨q⟩ := (reachable_deleteEdges_iff hnb).mpr hV
  -- `q` 的边都在 `F ∖ {e} ⊆ E(S)` 内 ⇒ 支撑 ⊆ `S`
  -- 逐条边看：`deleteEdges {e} ≤ fromEdgeSet F`，而 `F ⊆ E(S)` 给出两端在 `S` 内
  have hedgeS : ∀ f ∈ q.edges, ∀ x ∈ f, x ∈ S := by
    intro f hf x hx
    -- `f` 是删边图的边 ⇒ `f ∈ F ∖ {e}`（Finset 层面），从而 `f ∈ F`
    have h1 : f ∈ ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).deleteEdges {e}).edgeSet :=
      SimpleGraph.Walk.edges_subset_edgeSet q hf
    rw [SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_fromEdgeSet] at h1
    -- `h1 : f ∈ (↑F \ diagSet) \ {e}`；剥两层集合差得 `f ∈ F`
    have h2 : f ∈ F := by
      have hmem : f ∈ (↑F : Set (Sym2 V)) :=
        Set.mem_of_mem_sdiff (Set.mem_of_mem_sdiff h1)
      exact Finset.mem_coe.mp hmem
    exact mem_of_mem_edgeWithin (hF h2) x hx
  refine ⟨q.induce _ (fun x hx => ?_)⟩
  -- 支撑上的点：要么是终点，要么是某条边的端点
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hx
  rcases hx with h | ⟨f, hf, hxf⟩
  · exact h ▸ w.2
  · exact hedgeS f hf x hxf

/-- **对合的一步（加边方向）**：`F` 连通生成 ⇒ `F ∪ {e}` 连通生成。
加边只会**增加**可及性（`fromEdgeSet F ≤ fromEdgeSet (F ∪ {e})`），故连通性保持。
（不需要 `e ∉ F`，也不需要 `e ∈ E(S)`。） -/
theorem connected_spanning_insert {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {e : Sym2 V}
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    ((SimpleGraph.fromEdgeSet (↑(F ∪ {e}) : Set (Sym2 V))).induce (↑S : Set V)).Connected := by
  -- 去掉 `induce` 的一层：只需在 `S` 上证明连通
  refine hconn.mono ?_
  -- `fromEdgeSet F ≤ fromEdgeSet (F ∪ {e})`
  intro u v huv
  rw [SimpleGraph.induce_adj] at huv ⊢
  -- 先把 `huv` 拆成"边在 `F` 内"与"两端不同"
  obtain ⟨hmem, hne⟩ := (SimpleGraph.fromEdgeSet_adj (s := (↑F : Set (Sym2 V)))).mp huv
  have hmemF : (s(↑u, ↑v) : Sym2 V) ∈ F := hmem
  rw [SimpleGraph.fromEdgeSet_adj]
  exact ⟨Finset.mem_union_left _ hmemF, hne⟩

/-! ##### 对合装配：非割边项两两相消 -/

/-- **对合的成对性**：`F ⊆ E(S)`、`F` 连通生成、`e ∉ F` ⇒
`F ∪ {e}` 也连通生成，且 `e ∈ F ∪ {e}`、`(F ∪ {e}) ∖ {e} = F`。

（这就是 `F ↦ F ∆ {e}` 在"`e ∉ F`"一侧的显式形式——用 `∪ {e}` 而非 `∆` 更便于记账。） -/
theorem union_singleton_roundtrip {F : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ F) :
    (F ∪ {e}) \ {e} = F := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact hx
    · exact absurd hx hne
  · intro hx
    exact ⟨Or.inl hx, fun h => he (h ▸ hx)⟩

/-! ##### 非割边项的相消

把连通生成子图按 `e` 是否为其割边分成两类。`e` 非割边的那类由
`F ↦ F ∪ {e}`（`e ∉ F` 一侧）与其逆（`e ∈ F` 一侧，用 `erase_of_not_isBridge`）
**一一配对**，且两侧 `|F|` 相差 1 ⇒ 符号相消。

下面给出配对本身（不做求和）：`e` 非割边的连通生成子图与"不含 `e` 的连通生成子图"
之间存在双射。 -/

/-- **配对的正向**：`e ∉ F`、`F` 连通生成 ⇒ `F ∪ {e}` 连通生成且 `e` 在其内、
并且 `e` **不是** `F ∪ {e}` 的割边（因为删掉 `e` 后 `F` 仍在）。

这条把"`e ∉ F`"一侧送到"`e ∈ F` 且 `e` 非割边"一侧。 -/
theorem union_singleton_connected_not_bridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ F)
    (heS : e ∈ edgeWithin I S) (hF : F ⊆ edgeWithin I S)
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    e ∈ F ∪ {e} ∧ (F ∪ {e}) ⊆ edgeWithin I S ∧
      ((SimpleGraph.fromEdgeSet (↑(F ∪ {e}) : Set (Sym2 V))).induce (↑S : Set V)).Connected ∧
      ¬ (SimpleGraph.fromEdgeSet (↑(F ∪ {e}) : Set (Sym2 V))).IsBridge e := by
  refine ⟨Finset.mem_union_right _ (Finset.mem_singleton_self e),
    Finset.union_subset hF (Finset.singleton_subset_iff.mpr heS),
    connected_spanning_insert (I := I) hconn, ?_⟩
  -- `e` 不是 `F ∪ {e}` 的割边：删掉 `e` 后得到 `F`，它连通 ⇒ 两端可达
  intro hbridge
  revert hbridge he heS
  refine Sym2.ind (fun a b => ?_) e
  intro he heS hbridge
  -- 此时目标里的 `e` 已换成 `s(a,b)`；在此重新导出 roundtrip
  have hEq : (F ∪ {s(a, b)}) \ {s(a, b)} = F := union_singleton_roundtrip he
  rw [SimpleGraph.isBridge_iff] at hbridge
  -- `hbridge : ¬ (…deleteEdges {s(a,b)}).Reachable a b`；但该图就是 `fromEdgeSet F`
  apply hbridge
  have hgraph : (SimpleGraph.fromEdgeSet (↑(F ∪ {s(a, b)}) : Set (Sym2 V))).deleteEdges
      {s(a, b)} = SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V)) := by
    rw [deleteEdges_fromEdgeSet_singleton (F := F ∪ {s(a, b)}) (e := s(a, b)), hEq]
  rw [hgraph]
  -- `a`、`b` 都在 `S` 内（`e = s(a,b) ∈ E(S)`），且 `F` 在 `S` 上连通
  have haS : a ∈ S := mem_of_mem_edgeWithin heS a (Sym2.mem_iff.mpr (Or.inl rfl))
  have hbS : b ∈ S := mem_of_mem_edgeWithin heS b (Sym2.mem_iff.mpr (Or.inr rfl))
  exact (hconn ⟨a, haS⟩ ⟨b, hbS⟩).elim fun p =>
    ⟨p.map (SimpleGraph.Embedding.induce _).toHom⟩

/-! ##### 非割边项的和为零（`Finset.sum_involution`） -/

/-- **非割边部分相消**：在"连通生成 ∧ `e` 非 `F` 的割边"的 `F` 上，
`Σ (−1)^{|F|} = 0`。

用 `Finset.sum_involution`：取对合 `g F = F ∪ {e}`（当 `e ∉ F`）、`F ∖ {e}`（当 `e ∈ F`）。
三项义务由 `union_singleton_connected_not_bridge`（正向）、
`connected_spanning_erase_of_not_isBridge`（反向）与
`Finset.card_union_of_disjoint` + `pow_succ`（符号相反）给出。 -/
theorem sum_neg_one_pow_of_not_bridge_eq_zero {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {e : Sym2 V} (heS : e ∈ edgeWithin I S) :
    (∑ F ∈ (edgeWithin I S).powerset.filter (fun F : Finset (Sym2 V) =>
        ((SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).induce (S : Set V)).Connected ∧
        ¬ (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsBridge e),
      (-1 : ℤ) ^ F.card) = 0 := by
  refine Finset.sum_involution
    (fun F _ => if e ∈ F then F \ {e} else F ∪ {e}) ?_ ?_ ?_ ?_
  · -- `f a + f (g a) = 0`：`g` 把基数改 1，故符号相反
    intro F hF
    obtain ⟨hFsub, hconn, hnb⟩ := Finset.mem_filter.mp hF
    have hFsub' : F ⊆ edgeWithin I S := Finset.mem_powerset.mp hFsub
    by_cases hmem : e ∈ F
    · -- `e ∈ F` ⇒ `g F = F∖{e}`；`(F∖{e}).card + 1 = F.card`
      rw [ite_eq_left hmem]
      have hcard : (F \ {e}).card + 1 = F.card := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_add_one hmem]
      rw [← hcard, pow_succ]
      ring
    · rw [ite_eq_right hmem]
      have hcard : (F ∪ {e}).card = F.card + 1 := by
        rw [Finset.card_union_of_disjoint]
        · simp
        · rw [Finset.disjoint_singleton_right]; exact hmem
      rw [hcard, pow_succ]
      ring
  · -- `f a ≠ 0` ⇒ `g a ≠ a`：`g` 改变基数，故不动点不存在
    intro F hF _
    by_cases hmem : e ∈ F
    · rw [ite_eq_left hmem]
      intro hEq
      -- `e ∉ F∖{e}`，故不可能等于 `F`（`e ∈ F`）
      have : e ∈ F \ {e} := hEq.symm ▸ hmem
      exact (Finset.mem_sdiff.mp this).2 (Finset.mem_singleton_self e)
    · rw [ite_eq_right hmem]
      intro hEq
      have h1 : e ∈ F ∪ {e} := Finset.mem_union_right _ (Finset.mem_singleton_self e)
      exact hmem (hEq ▸ h1)
  · -- `g` 落在索引集内
    intro F hF
    obtain ⟨hFsub, hconn, hnb⟩ := Finset.mem_filter.mp hF
    have hFsub' : F ⊆ edgeWithin I S := Finset.mem_powerset.mp hFsub
    by_cases hmem : e ∈ F
    · -- `F ∖ {e}` 仍连通生成（`e` 非割边）；且 `e ∉ F∖{e}` ⇒ `e` 更不可能是其割边
      rw [ite_eq_left hmem]
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset.trans hFsub'),
        connected_spanning_erase_of_not_isBridge hFsub' hnb hconn, ?_⟩
      -- `e ∉ F∖{e}` ⇒ 删边图 = 原图；而原图在 `S` 上连通 ⇒ `e` 的两端可达 ⇒ 非割边
      intro hbridge
      -- 把 `e` 写成 `s(a,b)` 以便用 `isBridge_iff`（`hsame`、`heS`、`hnb` 一并重建）
      revert hbridge heS hnb
      refine Sym2.ind (fun a b => ?_) e
      intro heS hnb hbridge
      have hsame : (SimpleGraph.fromEdgeSet (↑(F \ {s(a, b)}) : Set (Sym2 V))).deleteEdges
          {s(a, b)} = SimpleGraph.fromEdgeSet (↑(F \ {s(a, b)}) : Set (Sym2 V)) := by
        rw [deleteEdges_fromEdgeSet_singleton]
        congr 1
        -- `(F ∖ {s(a,b)}) ∖ {s(a,b)} = F ∖ {s(a,b)}`
        simp
      rw [SimpleGraph.isBridge_iff] at hbridge
      apply hbridge
      rw [hsame]
      -- `a`、`b` 都在 `S` 内（`e = s(a,b) ∈ E(S)`），`F∖{s(a,b)}` 在 `S` 上连通
      have haS : a ∈ S := mem_of_mem_edgeWithin heS a (Sym2.mem_iff.mpr (Or.inl rfl))
      have hbS : b ∈ S := mem_of_mem_edgeWithin heS b (Sym2.mem_iff.mpr (Or.inr rfl))
      have hconn' : ((SimpleGraph.fromEdgeSet (↑(F \ {s(a, b)}) : Set (Sym2 V))).induce
          (↑S : Set V)).Connected :=
        connected_spanning_erase_of_not_isBridge hFsub' hnb hconn
      exact (hconn' ⟨a, haS⟩ ⟨b, hbS⟩).elim fun p =>
        ⟨p.map (SimpleGraph.Embedding.induce _).toHom⟩
    · -- `F ∪ {e}`：由正向引理直接给出
      rw [ite_eq_right hmem]
      obtain ⟨-, hsub', hconn', hnb'⟩ :=
        union_singleton_connected_not_bridge hmem heS hFsub' hconn
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub', hconn', hnb'⟩
  · -- `g` 是对合
    intro F hF
    by_cases hmem : e ∈ F
    · rw [ite_eq_left hmem]
      -- `g (F∖{e})`：`e ∉ F∖{e}` ⇒ 取右支 ⇒ `(F∖{e}) ∪ {e} = F`
      rw [ite_eq_right (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton_self e))]
      exact Finset.sdiff_union_of_subset (Finset.singleton_subset_iff.mpr hmem)
    · rw [ite_eq_right hmem]
      -- `g (F ∪ {e})`：`e ∈ F∪{e}` ⇒ 取左支 ⇒ `(F∪{e}) ∖ {e} = F`
      rw [ite_eq_left (Finset.mem_union_right _ (Finset.mem_singleton_self e))]
      exact union_singleton_roundtrip hmem

/-! ##### 归约：`connSum` 只剩"`e` 为割边"的项 -/

/-- **`connSum` 的割边归约**：对 `e ∈ E(S)`，

`connSum I S = Σ_{F ⊆ E(S), F 连通生成, e 是 F 的割边} (−1)^{|F|}`。

由 `connSum` 的定义 + 按"`e` 是否 `F` 的割边"二分 + 非割边部分为零
（`sum_neg_one_pow_of_not_bridge_eq_zero`）得到。 -/
theorem connSum_eq_sum_of_isBridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {e : Sym2 V} (heS : e ∈ edgeWithin I S) :
    connSum I S = ∑ F ∈ (edgeWithin I S).powerset.filter (fun F : Finset (Sym2 V) =>
        ((SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).induce (S : Set V)).Connected ∧
        (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsBridge e),
      (-1 : ℤ) ^ F.card := by
  rw [connSum]
  -- 把 `if conn then (-1)^|F| else 0` 按 `conn ∧ bridge` / `conn ∧ ¬bridge` 二分
  have hsplit : (∑ F ∈ (edgeWithin I S).powerset,
        if ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected
          then (-1 : ℤ) ^ F.card else 0)
      = (∑ F ∈ (edgeWithin I S).powerset.filter (fun F : Finset (Sym2 V) =>
            ((SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).induce (S : Set V)).Connected ∧
            (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsBridge e),
          (-1 : ℤ) ^ F.card)
        + (∑ F ∈ (edgeWithin I S).powerset.filter (fun F : Finset (Sym2 V) =>
            ((SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).induce (S : Set V)).Connected ∧
            ¬ (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsBridge e),
          (-1 : ℤ) ^ F.card) := by
    -- 先把被积项写成"桥与否"的 `if`，再用 `sum_filter_add_sum_filter_not`
    have hcongr : ∀ F : Finset (Sym2 V),
        (if ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected
          then (-1 : ℤ) ^ F.card else 0)
        = (if ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected ∧
              (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsBridge e
            then (-1 : ℤ) ^ F.card else 0)
          + (if ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected ∧
                ¬ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsBridge e
              then (-1 : ℤ) ^ F.card else 0) := by
      intro F
      by_cases hc : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected
      · by_cases hb : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsBridge e <;>
          simp [hc, hb]
      · simp [hc]
    rw [Finset.sum_congr rfl (fun F _ => hcongr F)]
    rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
  rw [hsplit, sum_neg_one_pow_of_not_bridge_eq_zero heS, add_zero]

/-! ##### 割边因子化（最后归纳的引擎）

设 `e = s(a,b) ∈ E(S)` 是**图** `(fromEdgeSet (E(S))).induce S` 的割边。
令 `S₁` = 删掉 `e` 后 `a` 所在的连通块、`S₂ = S ∖ S₁`。则
`S = S₁ ⊔ S₂`、`a ∈ S₁`、`b ∈ S₂`，且

> `connSum I S = − connSum I S₁ · connSum I S₂`

机制：连通生成子图必含割边 `e`（它贡献一个 `−1` 因子），其余部分在 `S₁`、`S₂`
上各自独立地遍历"连通生成子图"。

**先证拆分的两个几何事实**（顶点层面）。 -/

omit [LinearOrder V] in
/-- **割边拆分的基本事实**：`e = s(a,b)` 是图 `G` 的割边 ⇒
在 `G.deleteEdges {e}` 里，`a` 与 `b` **不可达**。 -/
theorem not_reachable_of_isBridge {G : SimpleGraph V} {a b : V}
    (hb : G.IsBridge s(a, b)) :
    ¬ (G.deleteEdges {s(a, b)}).Reachable a b :=
  (SimpleGraph.isBridge_iff).mp hb

omit [LinearOrder V] in
/-- **割边两侧**：`e = s(a,b)` 是 `G` 的割边时，删掉 `e` 后 `a` 的可达集
**不含** `b`。这是 `S₁`、`S₂` 的定义性事实（`S₂ = S ∖ S₁` 自动把 `b` 划到另一侧）。

（不需要 `S₁ ∪ S₂ = S` 的一般证明：取 `S₁` 为"删边图中与 `a` 可达的 `S` 内顶点"，
则 `b ∉ S₁` 由此引理给出；`S₂ := S ∖ S₁` 便含 `b`。） -/
theorem not_mem_reachSet_of_isBridge {G : SimpleGraph V} {a b : V} {S : Finset V}
    (hb : G.IsBridge s(a, b)) :
    b ∉ S.filter (fun x => (G.deleteEdges {s(a, b)}).Reachable a x) := by
  simp only [Finset.mem_filter, not_and]
  intro _
  exact not_reachable_of_isBridge hb

omit [LinearOrder V] in
/-- **连通生成子图必含图割边**：`e` 是 `G := fromEdgeSet (E(S))` 在 `S` 上的割边，
`F ⊆ E(S)` 在 `S` 上连通生成 ⇒ `e ∈ F`。

若 `e ∉ F`，则 `fromEdgeSet F ≤ fromEdgeSet (E(S) ∖ {e})`，而 `F` 的连通性给出
`e` 两端在删边图里的可达性 —— 与 `e` 是割边矛盾。

**注**：这里 `F` 的连通性用到 `fromEdgeSet F ≤ G`（`F ⊆ E(S)`）与 `G` 的割边性。 -/
theorem mem_of_connected_of_isBridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {e : Sym2 V} (heS : e ∈ edgeWithin I S)
    (hF : F ⊆ edgeWithin I S)
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected)
    (hbridge : (SimpleGraph.fromEdgeSet (↑(edgeWithin I S) : Set (Sym2 V))).IsBridge e) :
    e ∈ F := by
  by_contra hmem
  revert hbridge hconn hmem heS
  refine Sym2.ind (fun a b => ?_) e
  -- 实测 intro 顺序 = `heS`, 连通性, 割边性, 非成员性（即 revert 的**正序**）
  intro heS hconn' hbridge' hmem'
  rw [SimpleGraph.isBridge_iff] at hbridge'
  -- `a`、`b` 都在 `S` 内
  have haS : a ∈ S := mem_of_mem_edgeWithin heS a (Sym2.mem_iff.mpr (Or.inl rfl))
  have hbS : b ∈ S := mem_of_mem_edgeWithin heS b (Sym2.mem_iff.mpr (Or.inr rfl))
  -- `F` 在 `S` 上连通 ⇒ 在 `V` 层面 `a`、`b` 在 `fromEdgeSet F` 里可达
  have hreach : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable a b := by
    obtain ⟨p⟩ := hconn' ⟨a, haS⟩ ⟨b, hbS⟩
    exact ⟨p.map (SimpleGraph.Embedding.induce _).toHom⟩
  -- `e ∉ F` ⇒ `fromEdgeSet F ≤ (fromEdgeSet (E(S))).deleteEdges {e}`，故删边图里也可达
  apply hbridge'
  refine hreach.mono ?_
  intro x y hxy
  rw [SimpleGraph.fromEdgeSet_adj] at hxy
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨hF hxy.1, hxy.2⟩
  · -- `s(x,y) ∉ {e}`：因 `e ∉ F` 而 `s(x,y) ∈ F`
    intro hEq
    exact hmem' (hEq ▸ hxy.1)

/-! ##### 割边的"两侧"与跨边结构

设 `e = s(a,b)` 是 `G := (fromEdgeSet (E(S))).induce S` 的割边。定义

* `S₁ := S.filter (fun x => (G.deleteEdges {e}).Reachable a x)`（含 `a`，不含 `b`）
* `S₂ := S ∖ S₁`（含 `b`）

则 `S = S₁ ⊔ S₂`，且**任何跨 `S₁`/`S₂` 的 `E(S)`-边都只能是 `e` 本身** ——
这正是"割边"的含义，也是双射的几何内容。

下面先证后一条（它给出 `F∖{e}` 不会跨两侧）。 -/

omit [LinearOrder V] in
/-- **`E(S)` 的跨侧边只有 `e`**：若 `f ∈ E(S)`、`f` 的一端在 `S₁`、另一端在 `S₂`，
且 `f` 在删边图 `(fromEdgeSet (E(S))).deleteEdges {e}` 里**不被删**（即 `f ≠ e`），
则矛盾。

证明：`S₁` 成员的定义就是"在删边图里与 `a` 可达"；`f` 提供删边图里的一步，
把 `S₂` 侧那点也拉进 `S₁`。 -/
theorem cross_edge_eq_bridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {e f : Sym2 V} {a : V} {x y : V} (hy : y ∈ S)
    (hxy : (SimpleGraph.fromEdgeSet (↑(edgeWithin I S) : Set (Sym2 V))).Adj x y)
    (hxyf : (s(x, y) : Sym2 V) = f) (hf : f ≠ e)
    (hx1 : x ∈ S.filter (fun z =>
      ((SimpleGraph.fromEdgeSet (↑(edgeWithin I S) : Set (Sym2 V))).deleteEdges
        {e}).Reachable a z)) :
    y ∈ S.filter (fun z =>
      ((SimpleGraph.fromEdgeSet (↑(edgeWithin I S) : Set (Sym2 V))).deleteEdges
        {e}).Reachable a z) := by
  rw [Finset.mem_filter] at hx1 ⊢
  refine ⟨hy, ?_⟩
  -- `x` 在删边图里与 `a` 可达，而 `x — y` 这一步没被删（`f ≠ e`），故 `y` 也可达
  refine hx1.2.trans (SimpleGraph.Adj.reachable ?_)
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hxy, ?_⟩
  -- `s(x,y) = f ≠ e` ⇒ 这一步不在被删的 `{e}` 里
  intro hmem
  exact hf (hxyf.symm.trans (by simpa using hmem))

/-! ##### `S₁`/`S₂` 的定义与基本事实

为避免重复长表达式，先给"`E(S)` 删掉割边 `e` 后的图"一个局部记号（不导出，只在本节用）。 -/

/-- `E(S)` 在 `S` 上诱导出的图。 -/
abbrev edgeGraph (I : SimpleGraph V) [Fintype ↑I.edgeSet] (S : Finset V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (↑(edgeWithin I S) : Set (Sym2 V))

omit [LinearOrder V] in
/-- **割边一侧（含 `a` 的那侧）**：`E(S)` 删掉 `e` 后，`S` 内与 `a` 可达的顶点集。 -/
def sideOf (I : SimpleGraph V) [Fintype ↑I.edgeSet] (S : Finset V) (e : Sym2 V) (a : V) :
    Finset V :=
  S.filter (fun z => (edgeGraph I S).deleteEdges {e} |>.Reachable a z)

/-- **两侧合并回 `S`**：`sideOf` 与其在 `S` 中的补集拼回 `S`。 -/
theorem sideOf_union_sdiff {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    {e : Sym2 V} {a : V} :
    sideOf I S e a ∪ (S \ sideOf I S e a) = S :=
  Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

omit [LinearOrder V] in
/-- **`a` 在自己那一侧**。 -/
theorem mem_sideOf_self {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    {e : Sym2 V} {a : V} (ha : a ∈ S) : a ∈ sideOf I S e a :=
  Finset.mem_filter.mpr ⟨ha, SimpleGraph.Reachable.refl a⟩

omit [LinearOrder V] in
/-- **`F ∖ {e}` 的每条边都不跨两侧**：设 `e` 是 `E(S)` 在 `S` 上的割边、`f ∈ E(S)`、`f ≠ e`，
则 `f` 两端同属 `sideOf I S e a` 或同属其补集。

（只需 `f ∈ E(S)` 与 `f ≠ e`；连通性并非必需 —— 割边性已经把跨边限制死了。） -/
theorem not_cross_of_mem_of_connected {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {e f : Sym2 V} {a : V}
    (hfS : f ∈ edgeWithin I S) (hfe : f ≠ e) :
    (∀ x ∈ f, x ∈ sideOf I S e a) ∨ (∀ x ∈ f, x ∉ sideOf I S e a) := by
  -- 把 `f` 写成 `s(x,y)`；`f ∈ E(S)` 给出两端都在 `S` 内且在 `E(S)` 里相邻
  revert hfe hfS
  refine Sym2.ind (fun x y => ?_) f
  intro hfS hfe
  have hxS : x ∈ S := mem_of_mem_edgeWithin hfS x (Sym2.mem_iff.mpr (Or.inl rfl))
  have hyS : y ∈ S := mem_of_mem_edgeWithin hfS y (Sym2.mem_iff.mpr (Or.inr rfl))
  have hadj : (edgeGraph I S).Adj x y := by
    rw [edgeGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨hfS, fun h => by
      have h1 : (s(x, y) : Sym2 V) ∈ I.edgeSet := by
        rw [← SimpleGraph.mem_edgeFinset]
        exact (Finset.mem_filter.mp hfS).1
      exact SimpleGraph.not_isDiag_of_mem_edgeSet (G := I) h1 h⟩
  by_cases hx1 : x ∈ sideOf I S e a
  · left
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hx1
    · exact cross_edge_eq_bridge hyS hadj rfl hfe hx1
  · right
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hx1
    · intro hy1
      exact hx1 (cross_edge_eq_bridge hxS hadj.symm (by simp) hfe hy1)

/-! ##### 边集的跨侧劈分

`F ⊆ E(S)` 劈成"两端都在 `S₁`"与"两端都在 `S₂`"两块。由
`not_cross_of_mem_of_connected`，每条 `f ∈ F`、`f ≠ e` 恰好落在其中一块，
而 `e` 本身横跨两侧。 -/

/-- **劈分的并 = `G ∖ {e}`**：`G` 里除割边 `e = s(a,b)` 外的边，必落在
"两端在 `S₁`"或"两端不在 `S₁`"之一；而 `e` 本身两边都不落（`a ∈ S₁`、`b ∉ S₁`）。 -/
theorem filter_union_filter_eq_sdiff {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {G : Finset (Sym2 V)} {a b : V}
    (hG : G ⊆ edgeWithin I S) (hbridge : (edgeGraph I S).IsBridge s(a, b))
    (haS : a ∈ S) :
    (G.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a))
      ∪ (G.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a))
      = G \ {s(a, b)} := by
  ext f
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro (⟨hf, h1⟩ | ⟨hf, h2⟩)
    · refine ⟨hf, ?_⟩
      intro hfe
      subst hfe
      exact not_mem_reachSet_of_isBridge hbridge (h1 b (Sym2.mem_iff.mpr (Or.inr rfl)))
    · refine ⟨hf, ?_⟩
      intro hfe
      subst hfe
      exact h2 a (Sym2.mem_iff.mpr (Or.inl rfl)) (mem_sideOf_self haS)
  · rintro ⟨hfG, hfe⟩
    rcases not_cross_of_mem_of_connected (hG hfG) hfe with h | h
    · exact Or.inl ⟨hfG, h⟩
    · exact Or.inr ⟨hfG, h⟩

/-! ##### 连通性的跨侧传递

设 `e = s(a,b)` 是 `E(S)` 的割边、`F ⊆ E(S)` 在 `S` 上连通生成。
`F` **必含** `e`（`mem_of_connected_of_isBridge`），但 `e` 是唯一的跨边
（`not_cross_of_mem_of_connected`），所以 `F ∖ {e}` 的走步无法离开所在一侧：
要离开 `S₁` 只能走 `e`，而走了 `e` 就落在 `S₂`，再想回 `S₁` 又得跨一次 —— 不可能。

下面把"`S₁` 内部的走步不离开 `S₁`"证成独立引理。做法不是对 `Walk` 归纳
（case 太碎），而是**把走步搬到删边图上**：`F ∖ {e}` 的每条边都不跨侧，
于是可以直接用 `sideOf` 的定义做归纳。 -/

omit [LinearOrder V] in
/-- **只走"不跨侧"的边 ⇒ 留在 `S₁`**：若走步的每条边两端都在 `sideOf` 内，
则终点也在 `sideOf` 内。

用 `SimpleGraph.Walk` 的 `cons` 归纳：`cons` 一步给出 `(fromEdgeSet H).Adj u v₁`，
展开成 `s(u,v₁) ∈ H`，由 `hH` 得 `v₁ ∈ sideOf`，交给归纳假设。 -/
theorem mem_sideOf_of_walk {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    {e : Sym2 V} {a : V} {H : Finset (Sym2 V)}
    (hH : ∀ f ∈ H, ∀ x ∈ f, x ∈ sideOf I S e a)
    {u v : V} (hu : u ∈ sideOf I S e a)
    (p : (SimpleGraph.fromEdgeSet (↑H : Set (Sym2 V))).Walk u v) :
    v ∈ sideOf I S e a := by
  induction p with
  | nil => exact hu
  | cons hadj tail ih =>
    -- 把这一步的终点认出来：`hadj : (fromEdgeSet H).Adj u w`
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact ih (hH _ hadj.1 _ (Sym2.mem_iff.mpr (Or.inr rfl)))

/-! ##### 装配：`F` 的两半各自连通生成

设 `e = s(a,b)` 是 `E(S)` 在 `S` 上的割边、`F ⊆ E(S)` 在 `S` 上连通生成。
定义

* `F₁ := F.filter (fun f => ∀ x ∈ f, x ∈ S₁)`（`F` 中两端都在 `S₁` 的边）
* `F₂ := F.filter (fun f => ∀ x ∈ f, x ∉ S₁)`

则 `F₁ ∪ F₂ = F ∖ {e}`（`filter_union_filter_eq_sdiff`），
且 `F₁` 在 `S₁` 上连通生成、`F₂` 在 `S₂` 上连通生成。 -/

omit [LinearOrder V] in
/-- **一条"非割边"的跨侧传递**：`x ∈ S₁`、`s(x,y) ∈ F`、`s(x,y) ≠ e` ⇒ `y ∈ S₁`。

（`s(x,y) = e` 时结论为**假**（`a ∈ S₁` 而 `b ∉ S₁`），故必须排除；
在实际使用中割边那一步总由别的论证处理。） -/
theorem sideOf_of_mem_edge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b x y : V}
    (hF : F ⊆ edgeWithin I S)
    (hxy : (s(x, y) : Sym2 V) ∈ F) (hne : (s(x, y) : Sym2 V) ≠ s(a, b))
    (hx : x ∈ sideOf I S (s(a, b)) a) :
    y ∈ sideOf I S (s(a, b)) a := by
  rcases not_cross_of_mem_of_connected (hF hxy) hne with h | h
  · exact h y (Sym2.mem_iff.mpr (Or.inr rfl))
  · exact absurd hx (h x (Sym2.mem_iff.mpr (Or.inl rfl)))

/-! ##### 路径不经过割边（装配的**关键一步**）

⚠️ **两条被更正的假命题**（都记在 §4.17.17）：

1. "任何从 `S₁` 出发的 `F`-走步都留在 `S₁`" —— 假（走 `e` 就落到 `S₂`）；
2. "`S₁` 到 `S₁` 的 `F`-走步不经过 `e`" —— **也假**：走步可以是
   `a --e--> b --e--> a`（出去再回来），两端都在 `S₁` 却用了两次 `e`。

**正确的陈述必须用路径（无重复边）**：`p.IsPath`、两端都在 `S₁` ⇒ `e ∉ p.edges`。

**证法（两侧不变量 + 奇偶）**：

* 非 `e` 的边**保侧**（`sideOf_of_mem_edge` / `not_cross_of_mem_of_connected`）；
* `e` 这条边**翻侧**（`a ∈ S₁` 而 `b ∉ S₁`）；
* 起点、终点都在 `S₁` ⇒ `e` 出现次数**为偶**；
* `p.IsPath` ⇒ `p.IsTrail` ⇒ `p.edges.Nodup` ⇒ `e` 出现**至多一次**。

偶数且 ≤ 1 ⇒ **0 次**。 -/

omit [LinearOrder V] in
/-- **逐步的侧变换（两个方向分开写）**：设 `s(x,y) ∈ F`。

* 若 `s(x,y) ≠ e`：两端**同侧**；
* 若 `s(x,y) = e`：两端**异侧**（`a ∈ S₁`、`b ∉ S₁`）。

两者合起来就是"非 `e` 保侧、`e` 翻侧"。 -/
theorem sideOf_step_same {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b x y : V}
    (hF : F ⊆ edgeWithin I S)
    (hxy : (s(x, y) : Sym2 V) ∈ F) (hne : (s(x, y) : Sym2 V) ≠ s(a, b)) :
    (y ∈ sideOf I S (s(a, b)) a ↔ x ∈ sideOf I S (s(a, b)) a) := by
  rcases not_cross_of_mem_of_connected (hF hxy) hne with h | h
  · exact ⟨fun _ => h x (Sym2.mem_iff.mpr (Or.inl rfl)),
      fun _ => h y (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · exact ⟨fun hy => absurd hy (h y (Sym2.mem_iff.mpr (Or.inr rfl))),
      fun hx => absurd hx (h x (Sym2.mem_iff.mpr (Or.inl rfl)))⟩

omit [LinearOrder V] in
/-- **`e` 的两端分居两侧**：`a ∈ sideOf` 而 `b ∉ sideOf`。 -/
theorem not_mem_sideOf_b {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    b ∉ sideOf I S (s(a, b)) a :=
  not_mem_reachSet_of_isBridge hbridge

/-! ##### 侧不变量：两端同侧 ⇒ `e` 出现偶数次

对走步归纳，携带不变量

> `side(终点) = side(起点)` **当且仅当** `e` 在边表里出现**偶数**次。

* 非 `e` 的一步：`sideOf_step_same` 保侧，`e` 计数不变 ⇒ 不变量保持；
* `e` 的一步：两端异侧（`not_mem_sideOf_b`），计数 +1 ⇒ 奇偶翻转，不变量保持。

两端同侧 ⇒ 计数为**偶**；再配 `IsTrail.edges_nodup`（计数 ≤ 1）⇒ 计数 = 0。 -/

omit [LinearOrder V] in
/-- **`e` 的两端异侧（写出 `a`、`b` 的版本）**：`a ∈ S₁`、`b ∉ S₁`，故
`(x ∈ S₁ ↔ y ∈ S₁)` 在 `{x,y} = {a,b}` 时为**假**。 -/
theorem not_iff_sideOf_of_eq {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b x y : V} (haS : a ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b))
    (hEq : (s(x, y) : Sym2 V) = s(a, b)) :
    ¬ (x ∈ sideOf I S (s(a, b)) a ↔ y ∈ sideOf I S (s(a, b)) a) := by
  have hb_not : b ∉ sideOf I S (s(a, b)) a := not_mem_sideOf_b hbridge
  have ha_in : a ∈ sideOf I S (s(a, b)) a := mem_sideOf_self haS
  rcases (Sym2.eq_iff.mp hEq) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · intro hiff
    exact hb_not (h2 ▸ (hiff.mp (h1 ▸ ha_in)))
  · intro hiff
    exact hb_not (h1 ▸ (hiff.mpr (h2 ▸ ha_in)))

/-- **侧不变量**：`F` 上的走步两端同侧 ⟺ `e` 在边表里出现偶数次。 -/
theorem count_bridge_even_iff_same_side {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V} (haS : a ∈ S)
    (hF : F ⊆ edgeWithin I S) (hbridge : (edgeGraph I S).IsBridge s(a, b))
    {u v : V} (p : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Walk u v) :
    ((u ∈ sideOf I S (s(a, b)) a ↔ v ∈ sideOf I S (s(a, b)) a) ↔
      List.count (s(a, b)) p.edges % 2 = 0) := by
  induction p with
  | nil => simp
  | @cons x y z hadj tail ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    have hxy : (s(x, y) : Sym2 V) ∈ F := hadj.1
    by_cases hEq : (s(x, y) : Sym2 V) = s(a, b)
    · -- 这一边就是 `e`：计数 +1（奇偶翻转），两端**异**侧
      rw [SimpleGraph.Walk.edges_cons, hEq, List.count_cons_self]
      have hxy_opp := not_iff_sideOf_of_eq haS hbridge hEq
      -- 记 `c := List.count _ tail.edges`；`ih : (y↔z) ↔ c % 2 = 0`
      -- `¬(x↔y)` ⇒ `(x↔z) ↔ ¬(y↔z)`，而 `c` 与 `c+1` 奇偶互补
      have key : (x ∈ sideOf I S (s(a, b)) a ↔ z ∈ sideOf I S (s(a, b)) a)
          ↔ ¬ (y ∈ sideOf I S (s(a, b)) a ↔ z ∈ sideOf I S (s(a, b)) a) := by
        -- 记 `X := x ∈ S₁`、`Y := y ∈ S₁`、`Z := z ∈ S₁`；由 `hxy_opp` 有 `X ↔ ¬Y`。
        -- 于是 `(X ↔ Z) ↔ ¬(Y ↔ Z)` 是重言式 —— 对三者逐一分情形即可。
        by_cases hX : x ∈ sideOf I S (s(a, b)) a <;>
          by_cases hY : y ∈ sideOf I S (s(a, b)) a <;>
          by_cases hZ : z ∈ sideOf I S (s(a, b)) a <;>
          simp_all
      rw [key, ih]
      omega
    · -- 这一边不是割边：计数不变，两端**同**侧
      rw [SimpleGraph.Walk.edges_cons,
        List.count_cons_of_ne (b := s(x, y)) (a := s(a, b)) hEq]
      -- 把 `x ∈ S₁` 换成 `y ∈ S₁`（`sideOf_step_same`），再套归纳假设
      have hsame := sideOf_step_same hF hxy hEq
      rw [show (x ∈ sideOf I S (s(a, b)) a ↔ z ∈ sideOf I S (s(a, b)) a)
          = (y ∈ sideOf I S (s(a, b)) a ↔ z ∈ sideOf I S (s(a, b)) a) from by
        exact propext (iff_congr hsame.symm Iff.rfl)]
      exact ih

/-! ##### ★ 路径不经过割边（装配的关键一步）

由侧不变量（`count_bridge_even_iff_same_side`）：两端同侧 ⇒ `count e p.edges` 为**偶**；
由 `IsPath` ⇒ `IsTrail` ⇒ `edges.Nodup` ⇒ `count e p.edges ≤ 1`。
偶数且 ≤ 1 ⇒ `= 0` ⇒ `e ∉ p.edges`。 -/

/-- **★ 路径不经过割边**：`p.IsPath`、两端都在 `S₁` ⇒ `e ∉ p.edges`。

**注意必须是路径**：走步可以是 `a --e--> b --e--> a`（出去再回来），
两端都在 `S₁` 却用了两次 `e`；而路径无重复边，故两次不可能。 -/
theorem bridge_notMem_edges_of_isPath {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V} (haS : a ∈ S)
    (hF : F ⊆ edgeWithin I S) (hbridge : (edgeGraph I S).IsBridge s(a, b))
    {u v : V} (hu : u ∈ sideOf I S (s(a, b)) a) (hv : v ∈ sideOf I S (s(a, b)) a)
    (p : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Walk u v) (hp : p.IsPath) :
    s(a, b) ∉ p.edges := by
  -- 两端同侧 ⇒ 计数为偶
  have heven : List.count (s(a, b)) p.edges % 2 = 0 :=
    (count_bridge_even_iff_same_side haS hF hbridge p).mp ⟨fun _ => hv, fun _ => hu⟩
  -- 路径无重复边 ⇒ 计数 ≤ 1
  have hle : List.count (s(a, b)) p.edges ≤ 1 :=
    (List.nodup_iff_count_le_one.mp (hp.isTrail.edges_nodup)) (s(a, b))
  -- 偶数且 ≤ 1 ⇒ 0
  have hzero : List.count (s(a, b)) p.edges = 0 := by omega
  exact List.count_eq_zero.mp hzero

/-! ##### ★ 装配：`F₁` 在 `S₁` 上连通

由 `bridge_notMem_edges_of_isPath`：路径不含 `e`；再由 `sideOf_of_mem_edge`
（非割边保侧）知路径每条边的两端都在 `S₁` 内，故每条边都落在 `F₁` 里。 -/

omit [LinearOrder V] in
/-- **逐边搬运（起点假设显式）**：`F` 上的走步，若其**每条边都不是 `e`**、
且起点在 `S₁`，则它可搬成 `F₁` 上的走步（且终点仍在 `S₁`）。

（"每条边都不是 `e`"由 `bridge_notMem_edges_of_isPath` 提供；
把起点假设显式写出，归纳才走得通。） -/
theorem reachable_filter_of_walk_aux {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V}
    (hF : F ⊆ edgeWithin I S)
    {u v : V} (p : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Walk u v)
    (hno : ∀ f ∈ p.edges, f ≠ s(a, b))
    (hu : u ∈ sideOf I S (s(a, b)) a) :
    (SimpleGraph.fromEdgeSet
      (↑(F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)) :
        Set (Sym2 V))).Reachable u v ∧ v ∈ sideOf I S (s(a, b)) a := by
  induction p with
  | nil =>
    refine ⟨?_, hu⟩
    exact SimpleGraph.Reachable.refl _
  | @cons x y z hadj tail ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    -- 当前边不是 `e`
    have hne : (s(x, y) : Sym2 V) ≠ s(a, b) :=
      hno (s(x, y)) (by
        rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_self)
    -- 非割边保侧 ⇒ `y ∈ S₁`
    have hy : y ∈ sideOf I S (s(a, b)) a := sideOf_of_mem_edge hF hadj.1 hne hu
    -- 该边落在 `F₁` 里
    have hfilt : (s(x, y) : Sym2 V) ∈
        F.filter (fun f => ∀ z ∈ f, z ∈ sideOf I S (s(a, b)) a) :=
      Finset.mem_filter.mpr ⟨hadj.1, fun z hz => by
        rcases Sym2.mem_iff.mp hz with hz' | hz'
        · exact hz' ▸ hu
        · exact hz' ▸ hy⟩
    have hadjF₁ : (SimpleGraph.fromEdgeSet
        (↑(F.filter (fun f => ∀ z ∈ f, z ∈ sideOf I S (s(a, b)) a)) :
          Set (Sym2 V))).Adj x y := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨hfilt, hadj.2⟩
    obtain ⟨hreach, hv⟩ := ih (fun f hf => hno f (by
      rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hf)) hy
    exact ⟨(SimpleGraph.Adj.reachable hadjF₁).trans hreach, hv⟩

/-! ##### ★ 装配主引理（按**任意基点** `p` 陈述，两侧可共用）

设 `p` 是割边 `s(p, q)` 的一端、`p ∈ S`。则 `S_p := sideOf I S (s(p,q)) p`
（删边图中与 `p` 可达的 `S` 内顶点）上，
`F ∩ {两端都在 S_p 的边}` 在该侧连通生成。

把 `p` 取 `a` 或 `b` 就得到"两个半边各自连通生成" —— 无需写两遍。 -/

/-- **★ 装配主引理**：`p ∈ S`、`s(p,q)` 是 `E(S)` 的割边、`F ⊆ E(S)` 在 `S` 上连通生成
⇒ `F ∩ {两端都在 S_p 的边}` 在 `S_p` 上连通生成（`S_p := sideOf I S (s(p,q)) p`）。 -/
theorem connected_induce_filter_sideOf {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {p q : V} (hpS : p ∈ S)
    (hF : F ⊆ edgeWithin I S) (hbridge : (edgeGraph I S).IsBridge s(p, q))
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    ((SimpleGraph.fromEdgeSet
      (↑(F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(p, q)) p)) : Set (Sym2 V))).induce
        (↑(sideOf I S (s(p, q)) p) : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨p, mem_sideOf_self hpS⟩, fun w => ?_⟩
  have hw1 : w.1 ∈ sideOf I S (s(p, q)) p := Finset.mem_coe.mp w.2
  have hw2 : w.1 ∈ S := (Finset.mem_filter.mp hw1).1
  -- `F` 在 `S` 上连通 ⇒ 可达；用 `Reachable.map` 搬到 `V` 层面，再取**路径**
  have hreachV : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable p w.1 :=
    SimpleGraph.Reachable.map (SimpleGraph.Embedding.induce (↑S : Set V)).toHom
      (hconn ⟨p, hpS⟩ ⟨w.1, hw2⟩)
  obtain ⟨p', hp'⟩ := hreachV.exists_isPath
  -- 路径不含割边（两端同侧）
  have hnot : s(p, q) ∉ p'.edges :=
    bridge_notMem_edges_of_isPath hpS hF hbridge (mem_sideOf_self hpS) hw1 p' hp'
  -- 逐边搬运成该侧上的走步
  obtain ⟨hreach, -⟩ :=
    reachable_filter_of_walk_aux hF p' (fun f hf h => hnot (h ▸ hf)) (mem_sideOf_self hpS)
  -- 搬到 `induce S_p` 上
  obtain ⟨r⟩ := hreach
  refine ⟨r.induce _ ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with h | ⟨f, hf, hzf⟩
  · rw [h]
    exact w.2
  · have h1 : f ∈ F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(p, q)) p) := by
      have h2 := SimpleGraph.Walk.edges_subset_edgeSet r hf
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h2
      exact Set.mem_of_mem_sdiff h2
    exact Finset.mem_coe.mpr ((Finset.mem_filter.mp h1).2 z hzf)

/-! ##### `S₂` 侧：把主引理的基点取成 `b`

`s(p,q)` 的两个参数不过是 `Sym2` 的两个代表元，`s(a,b)` 与 `s(b,a)` **是同一个元素**，
故主引理对 `p := b`、`q := a` 直接可用 —— 两侧共用一条证明，无需重写。 -/

set_option maxHeartbeats 2000000 in
/-- **★ 另一侧同样连通生成**：主引理取基点 `p := b`。

即：`F ∩ {两端都在 S_b 的边}` 在 `S_b := sideOf I S (s(a,b)) b` 上连通生成。

（`s(b,a)` 与 `s(a,b)` 是 `Sym2` 的**两个代表元**，由 `Sym2.eq_swap` 相等 —— 是**命题级**
而非定义级，故需显式改写；另外 `sideOf` 的体较长，此处 `isDefEq` 需要更多心跳。） -/
theorem connected_induce_filter_sideOf_b {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V} (hbS : b ∈ S)
    (hF : F ⊆ edgeWithin I S) (hbridge : (edgeGraph I S).IsBridge s(a, b))
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    ((SimpleGraph.fromEdgeSet
      (↑(F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) b)) : Set (Sym2 V))).induce
        (↑(sideOf I S (s(a, b)) b) : Set V)).Connected := by
  -- `s(b,a) = s(a,b)`（`Sym2` 的交换性）
  have hswap : (s(b, a) : Sym2 V) = s(a, b) := Sym2.eq_swap
  have hbridge' : (edgeGraph I S).IsBridge s(b, a) := by
    rw [hswap]; exact hbridge
  have hgoal := connected_induce_filter_sideOf (p := b) (q := a) hbS hF hbridge' hconn
  rwa [hswap] at hgoal

/-! ##### 两半**不交**（基数簿记的前提）

`F₁` 要求"两端都在 `S₁`"，`F₂` 要求"两端都不在 `S₁`"—— 二者对同一条边不可能同时成立。 -/

omit [LinearOrder V] in
/-- **两半不交**：`F ∩ {两端在 S₁}` 与 `F ∩ {两端不在 S₁}` 无公共边。

（只需 `f` 有端点 —— 任何 `Sym2` 元素都非空，用 `Sym2.ind` 取一个端点即可。） -/
theorem disjoint_filter_sideOf {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {e : Sym2 V} {a : V} :
    Disjoint (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S e a))
      (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S e a)) := by
  rw [Finset.disjoint_left]
  intro f hf1 hf2
  have h1 := (Finset.mem_filter.mp hf1).2
  have h2 := (Finset.mem_filter.mp hf2).2
  -- 取 `f` 的一个端点：`Sym2` 元素总可写成 `s(x,y)`，取 `x`
  revert h1 h2
  refine Sym2.ind (fun x _ => ?_) f
  intro h1 h2
  exact h2 x (Sym2.mem_iff.mpr (Or.inl rfl)) (h1 x (Sym2.mem_iff.mpr (Or.inl rfl)))

/-! ##### ★ 反向：两半 + 割边 ⇒ 整体连通生成（双射的逆）

设 `F₁'` 在 `S₁` 上连通、`F₂'` 在 `S₂ := S ∖ S₁` 上连通，`e = s(a,b)`、`a ∈ S₁`、`b ∈ S₂`、
`S₁ ⊆ S`、`S₂ ⊆ S`。则 `F := F₁' ∪ F₂' ∪ {e}` 在 `S` 上连通。

**走步搬运三步次序**（§4.17.23）：`hc` 给的是**诱导图**走步 ⇒
`map`（映出 `V`）→ `mapLe`（提升图）→ `induce`（回 `S`）。
**不能**直接对 `q` 用 `mapLe`。 -/

set_option maxHeartbeats 2000000 in
/-- **★ 反向装配（连通性）**：两半各自连通 ⇒ 并上割边后整体连通。 -/
theorem connected_union_bridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S S₁ : Finset V} {F₁' F₂' : Finset (Sym2 V)} {a b : V} {e : Sym2 V}
    (haS₁ : a ∈ S₁) (hbS₂ : b ∈ S \ S₁) (haS : a ∈ S) (hbS : b ∈ S)
    (hsub₁ : S₁ ⊆ S) (hsub₂ : S \ S₁ ⊆ S)
    (hF₁ : F₁' ⊆ edgeWithin I S₁) (hF₂ : F₂' ⊆ edgeWithin I (S \ S₁))
    (he : e = s(a, b))
    (hc₁ : ((SimpleGraph.fromEdgeSet (↑F₁' : Set (Sym2 V))).induce (↑S₁ : Set V)).Connected)
    (hc₂ : ((SimpleGraph.fromEdgeSet (↑F₂' : Set (Sym2 V))).induce
      (↑(S \ S₁) : Set V)).Connected) :
    ((SimpleGraph.fromEdgeSet
      (↑(F₁' ∪ F₂' ∪ {e}) : Set (Sym2 V))).induce (↑S : Set V)).Connected := by
  -- 并集与两个图包含
  have he_mem : e ∈ F₁' ∪ F₂' ∪ {e} := by simp
  have hle₁ : SimpleGraph.fromEdgeSet (↑F₁' : Set (Sym2 V)) ≤
      SimpleGraph.fromEdgeSet (↑(F₁' ∪ F₂' ∪ {e}) : Set (Sym2 V)) := by
    intro x y hxy
    rw [SimpleGraph.fromEdgeSet_adj] at hxy ⊢
    exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hxy.1), hxy.2⟩
  have hle₂ : SimpleGraph.fromEdgeSet (↑F₂' : Set (Sym2 V)) ≤
      SimpleGraph.fromEdgeSet (↑(F₁' ∪ F₂' ∪ {e}) : Set (Sym2 V)) := by
    intro x y hxy
    rw [SimpleGraph.fromEdgeSet_adj] at hxy ⊢
    exact ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hxy.1), hxy.2⟩
  -- 并集每条边的端点都在 `S` 内
  have hsupp : ∀ f ∈ F₁' ∪ F₂' ∪ {e}, ∀ z ∈ f, z ∈ S := by
    intro f hf z hz
    rcases Finset.mem_union.mp hf with hf | hf
    · rcases Finset.mem_union.mp hf with hf | hf
      · exact hsub₁ (mem_of_mem_edgeWithin (hF₁ hf) z hz)
      · exact hsub₂ (mem_of_mem_edgeWithin (hF₂ hf) z hz)
    · rw [Finset.mem_singleton] at hf
      subst hf
      rw [he] at hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact haS
      · exact hbS
  -- 把裸图走步搬进目标图的诱导图：**返回类型是 `↥S` 的元素**，故 `hu`/`hv` 显式携带
  have lift₁ : ∀ {u v : V}, (SimpleGraph.fromEdgeSet (↑F₁' : Set (Sym2 V))).Walk u v →
      ∀ (hu : u ∈ S) (hv : v ∈ S),
      ((SimpleGraph.fromEdgeSet
        (↑(F₁' ∪ F₂' ∪ {e}) : Set (Sym2 V))).induce (↑S : Set V)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v q hu hv
    refine ⟨(q.mapLe hle₁).induce _ ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with h | ⟨f, hf, hzf⟩
    · rw [h]; exact hv
    · -- `f ∈ F₁'`：剥两层
      have h2 := SimpleGraph.Walk.edges_subset_edgeSet (q.mapLe hle₁) hf
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h2
      have h3 : f ∈ F₁' ∪ F₂' ∪ {e} := Set.mem_of_mem_sdiff h2
      exact hsupp f h3 z hzf
  have lift₂ : ∀ {u v : V}, (SimpleGraph.fromEdgeSet (↑F₂' : Set (Sym2 V))).Walk u v →
      ∀ (hu : u ∈ S) (hv : v ∈ S),
      ((SimpleGraph.fromEdgeSet
        (↑(F₁' ∪ F₂' ∪ {e}) : Set (Sym2 V))).induce (↑S : Set V)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v q hu hv
    refine ⟨(q.mapLe hle₂).induce _ ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with h | ⟨f, hf, hzf⟩
    · rw [h]; exact hv
    · have h2 := SimpleGraph.Walk.edges_subset_edgeSet (q.mapLe hle₂) hf
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h2
      have h3 : f ∈ F₁' ∪ F₂' ∪ {e} := Set.mem_of_mem_sdiff h2
      exact hsupp f h3 z hzf
  -- `a ≠ b`（`a ∈ S₁`、`b ∉ S₁`）
  have hab : a ≠ b := fun h => (Finset.mem_sdiff.mp hbS₂).2 (h ▸ haS₁)
  -- 割边在整体图里连接 `a`、`b`
  have habit : ((SimpleGraph.fromEdgeSet
      (↑(F₁' ∪ F₂' ∪ {e}) : Set (Sym2 V))).induce (↑S : Set V)).Adj
        ⟨a, haS⟩ ⟨b, hbS⟩ := by
    rw [SimpleGraph.induce_adj]
    -- 目标化为 `V` 层面的邻接：`(fromEdgeSet 并集).Adj a b`
    show (SimpleGraph.fromEdgeSet (↑(F₁' ∪ F₂' ∪ {e}) : Set (Sym2 V))).Adj a b
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨by rw [← he]; exact he_mem, hab⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨a, haS⟩, fun w => ?_⟩
  have hwS : w.1 ∈ S := w.2
  have hw' : w.1 ∈ S₁ ∨ w.1 ∈ S \ S₁ := by
    by_cases h : w.1 ∈ S₁
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hwS, h⟩)
  rcases hw' with hw₁ | hw₂
  · obtain ⟨q⟩ := hc₁ ⟨a, haS₁⟩ ⟨w.1, hw₁⟩
    exact lift₁ (q.map (SimpleGraph.Embedding.induce _).toHom) haS hwS
  · obtain ⟨q⟩ := hc₂ ⟨b, hbS₂⟩ ⟨w.1, hw₂⟩
    exact (SimpleGraph.Adj.reachable habit).trans
      (lift₂ (q.map (SimpleGraph.Embedding.induce _).toHom) hbS hwS)

/-! ##### ★ 基数簿记：`|F| = |F₁| + |F₂| + 1`

由

* `filter_union_filter_eq_sdiff`：`F₁ ∪ F₂ = F ∖ {e}`（`F₁`/`F₂` 是 `F` 按"两端在 `S₁`"劈开的两半）；
* `disjoint_filter_sideOf`：`F₁`、`F₂` 不交；
* `mem_of_connected_of_isBridge`：`F` 连通生成 ⇒ `e ∈ F`

得 `|F ∖ {e}| = |F₁| + |F₂|`，而 `|F ∖ {e}| = |F| − 1`（因 `e ∈ F`）。 -/

/-- **★ 基数公式**：`|F| = |F₁| + |F₂| + 1`。

这是符号簿记 `(−1)^{|F|} = −(−1)^{|F₁|}(−1)^{|F₂|}` 的直接前提。 -/
theorem card_eq_card_filter_add_card_filter_add_one {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V}
    (heS : s(a, b) ∈ edgeWithin I S) (haS : a ∈ S)
    (hF : F ⊆ edgeWithin I S) (hbridge : (edgeGraph I S).IsBridge s(a, b))
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    F.card
      = (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)).card
        + (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)).card + 1 := by
  -- `e ∈ F`（连通生成子图必含割边）
  have heF : s(a, b) ∈ F :=
    mem_of_connected_of_isBridge (I := I) (S := S) (F := F) (e := s(a, b))
      heS hF hconn hbridge
  -- 两半不交 ⇒ 基数相加
  have hdisj : Disjoint (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a))
      (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) :=
    disjoint_filter_sideOf (I := I) (S := S) (F := F) (e := s(a, b)) (a := a)
  have hcard_union :
      ((F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a))
        ∪ (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a))).card
      = (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)).card
        + (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)).card :=
    Finset.card_union_of_disjoint hdisj
  -- 并 = `F ∖ {e}`
  rw [filter_union_filter_eq_sdiff hF hbridge haS] at hcard_union
  -- `F ∖ {e} = F.erase e`，其基数为 `|F| − 1`
  rw [Finset.sdiff_singleton_eq_erase,
    Finset.card_erase_of_mem heF] at hcard_union
  -- `F.card ≥ 1`（因 `e ∈ F`），故 `F.card - 1 = c₁ + c₂` ⇒ `F.card = c₁ + c₂ + 1`
  have hpos : 1 ≤ F.card := Finset.card_pos.mpr ⟨s(a, b), heF⟩
  omega

/-- **★ 符号簿记**：`(−1)^{|F|} = −(−1)^{|F₁|}·(−1)^{|F₂|}`。

由基数公式 `|F| = |F₁| + |F₂| + 1` 与 `(−1)^{a+b+1} = −(−1)^a(−1)^b` 直接得到；
这就是"割边贡献一个 `−1` 因子"的代数形式。 -/
theorem neg_one_pow_card_eq_neg_mul {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V}
    (heS : s(a, b) ∈ edgeWithin I S) (haS : a ∈ S)
    (hF : F ⊆ edgeWithin I S) (hbridge : (edgeGraph I S).IsBridge s(a, b))
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    (-1 : ℤ) ^ F.card
      = -((-1 : ℤ) ^ (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)).card
          * (-1 : ℤ) ^ (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)).card) := by
  rw [card_eq_card_filter_add_card_filter_add_one heS haS hF hbridge hconn, pow_succ, pow_add]
  ring

/-! ##### ★ 边集的不交分解：`E(S) ∖ {e} = E(S₁) ⊔ E(S₂)`

`S₁ := sideOf I S e a`、`S₂ := S ∖ S₁`、`e := s(a,b)` 是 `E(S)` 的割边。

* `S₁ ∪ S₂ = S`（`sideOf_union_sdiff`），故由 `edgeWithin_union_eq`（只需"无跨界边"）
  得 `E(S) = E(S₁) ∪ E(S₂)`；
* 而 `E(S₁) ∩ E(S₂) = ∅`（`edgeWithin_disjoint` + `Disjoint S₁ S₂`）。 -/

/-! ##### ★ 边集的不交分解：`E(S) ∖ {e} = E(S₁) ⊔ E(S₂)`

`S₁ := sideOf I S e a`、`S₂ := S ∖ S₁`、`e := s(a,b)` 是 `E(S)` 的割边。

* `S₁ ∪ S₂ = S`（`sideOf_union_sdiff`），故由 `edgeWithin_union_eq`（只需"无跨界边"）
  得 `E(S) = E(S₁) ∪ E(S₂)`；
* 而 `E(S₁) ∩ E(S₂) = ∅`（`edgeWithin_disjoint` + `Disjoint S₁ S₂`）。 -/

/-! ##### ★ 边集的不交分解：`E(S) = E(S₁) ⊔ E(S₂) ⊔ {e}`

`S₁ := sideOf I S e a`、`S₂ := S ∖ S₁`、`e := s(a,b)` 是 `E(S)` 的割边。

**关键修正**：`E(S₁) ∪ E(S₂)` 只是 `E(S)` 中**去掉 `e`** 的部分 ——
割边 `e` 本身两端正是一在 `S₁`、一在 `S₂`（`mem_sideOf_self` / `not_mem_sideOf_b`），
所以它**不能**被 `edgeWithin_union_eq` 的无跨边假设覆盖。正确分解是

> `E(S₁) ∪ E(S₂) ∪ {e} = E(S)`，且三者两两不交。

于是 `E(S) ∖ {e} = E(S₁) ⊔ E(S₂)`。 -/

@[simp] theorem sideOf_union_sdiff_self {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {e : Sym2 V} {a : V} :
    sideOf I S e a ∪ (S \ sideOf I S e a) = S :=
  sideOf_union_sdiff

/-! ##### ★ 边集的不交分解：`E(S) = E(S₁) ∪ E(S₂) ∪ {e}` -/

omit [LinearOrder V] in
/-- `S₁ := sideOf I S e a` 时，`S₁ ⊆ S`。 -/
theorem sideOf_subset {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    {e : Sym2 V} {a : V} : sideOf I S e a ⊆ S :=
  Finset.filter_subset _ _

/-- `S ∖ S₁ ⊆ S`。 -/
theorem sdiff_sideOf_subset {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    {e : Sym2 V} {a : V} : S \ sideOf I S e a ⊆ S :=
  Finset.sdiff_subset

/-- **★ 边集分解（`⊆` 方向）**：`f ∈ E(S)`、`f ≠ s(a,b)` ⇒
`f ∈ E(S₁)` 或 `f ∈ E(S₂)`。（只需 `f ∈ E(S)` 与 `f ≠ e`：`not_cross_of_mem_of_connected`
已经说明 `E(S)` 中除 `e` 外的边都不跨两侧。） -/
theorem mem_edgeWithin_sideOf_or_eq {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} {f : Sym2 V}
    (hfS : f ∈ edgeWithin I S) (hfe : f ≠ s(a, b)) :
    f ∈ edgeWithin I (sideOf I S (s(a, b)) a)
      ∨ f ∈ edgeWithin I (S \ sideOf I S (s(a, b)) a) := by
  rcases not_cross_of_mem_of_connected (e := s(a, b)) (a := a) hfS hfe with h | h
  · refine Or.inl (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hfS).1, h⟩)
  · refine Or.inr (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hfS).1, ?_⟩)
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨mem_of_mem_edgeWithin hfS v hv, h v hv⟩

/-- **★ 两侧内部边集不交**：`E(S₁) ∩ E(S₂) = ∅`（`S₁`、`S₂` 不交）。 -/
theorem disjoint_edgeWithin_sideOf {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {e : Sym2 V} {a : V} :
    Disjoint (edgeWithin I (sideOf I S e a)) (edgeWithin I (S \ sideOf I S e a)) :=
  edgeWithin_disjoint Finset.disjoint_sdiff

/-- **★ 边集分解（完整等式）**：`E(S₁) ∪ E(S₂) ∪ {e} = E(S)`。

* `⊆`：`edgeWithin_mono`（`S₁ ⊆ S`、`S₂ ⊆ S`）与 `e ∈ E(S)`；
* `⊇`：`mem_edgeWithin_sideOf_or_eq`，`f = e` 走 `{e}` 支。 -/
theorem edgeWithin_union_sideOf_eq {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (heS : s(a, b) ∈ edgeWithin I S) :
    edgeWithin I (sideOf I S (s(a, b)) a)
      ∪ edgeWithin I (S \ sideOf I S (s(a, b)) a) ∪ {s(a, b)} = edgeWithin I S := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · rcases Finset.mem_union.mp hf with hf | hf
      · exact edgeWithin_mono sideOf_subset hf
      · exact edgeWithin_mono sdiff_sideOf_subset hf
    · rw [Finset.mem_singleton.mp hf]; exact heS
  · intro f hf
    by_cases hfe : f = s(a, b)
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hfe)
    · exact Finset.mem_union_left _
        (Finset.mem_union.mpr (mem_edgeWithin_sideOf_or_eq hf hfe))

omit [LinearOrder V] in
/-- **`e ∉ E(S₁)`**：`b ∈ s(a,b)` 而 `b ∉ S₁`。 -/
theorem not_mem_edgeWithin_sideOf_b {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    s(a, b) ∉ edgeWithin I (sideOf I S (s(a, b)) a) :=
  fun h => not_mem_sideOf_b hbridge (mem_of_mem_edgeWithin h (b) (Sym2.mem_iff.mpr (Or.inr rfl)))

/-- **`e ∉ E(S₂)`**：`a ∈ s(a,b)` 而 `a ∉ S ∖ S₁`（`a ∈ S₁`）。 -/
theorem not_mem_edgeWithin_sdiff_sideOf {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (haS : a ∈ S) :
    s(a, b) ∉ edgeWithin I (S \ sideOf I S (s(a, b)) a) :=
  fun h => (Finset.mem_sdiff.mp (mem_of_mem_edgeWithin h a (Sym2.mem_iff.mpr (Or.inl rfl)))).2
    (mem_sideOf_self haS)

/-- **★ 和之劈分的第一步**：`E(S) ∖ {e} = E(S₁) ∪ E(S₂)`。 -/
theorem edgeWithin_sdiff_eq_union {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (haS : a ∈ S) (heS : s(a, b) ∈ edgeWithin I S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    edgeWithin I S \ {s(a, b)}
      = edgeWithin I (sideOf I S (s(a, b)) a)
        ∪ edgeWithin I (S \ sideOf I S (s(a, b)) a) := by
  have hdecomp := edgeWithin_union_sideOf_eq (I := I) (S := S) (a := a) (b := b) heS
  -- `E(S) = A ∪ B ∪ {e}` ⇒ `E(S) ∖ {e} = (A ∪ B ∪ {e}) ∖ {e}`，而 `e ∉ A ∪ B`
  rw [← hdecomp]
  ext f
  simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_union]
  constructor
  · rintro ⟨(hfA | hfB) | hfe, hne⟩
    · exact Or.inl hfA
    · exact Or.inr hfB
    · exact absurd hfe hne
  · rintro (hfA | hfB)
    · exact ⟨Or.inl (Or.inl hfA), fun h => not_mem_edgeWithin_sideOf_b hbridge (h ▸ hfA)⟩
    · exact ⟨Or.inl (Or.inr hfB), fun h => not_mem_edgeWithin_sdiff_sideOf haS (h ▸ hfB)⟩

/-! ##### ★ 连通生成边集的**两半分解**

设 `e = s(a,b)` 是 `E(S)` 的割边、`S₁ := sideOf I S e a`、`S₂ := S ∖ S₁`。
连通生成子图的边集 `F ⊆ E(S)` 必含 `e`（`mem_of_connected_of_isBridge`），
且 `F ∖ {e} ⊆ E(S₁) ⊔ E(S₂)`（`edgeWithin_sdiff_eq_union`），故

> `F = {e} ⊔ (F ∩ E(S₁)) ⊔ (F ∩ E(S₂))`（三者两两不交）。 -/

/-- `F ∖ {e}` 按"两端在 `S₁` / 不在 `S₁`"劈成两块（`e` 是 `E(S)` 的割边）。 -/
theorem mem_filter_sideOf_of_mem_sdiff {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} {F : Finset (Sym2 V)} (hF : F ⊆ edgeWithin I S)
    (haS : a ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    F \ {s(a, b)}
      = (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a))
        ∪ (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro f hf
    obtain ⟨hfF, hfne⟩ := Finset.mem_sdiff.mp hf
    have hfE := hF hfF
    rw [Finset.mem_singleton] at hfne
    rcases not_cross_of_mem_of_connected (e := s(a, b)) (a := a) hfE hfne with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hfF, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hfF, h⟩)
  · intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨hfF, h1⟩ := Finset.mem_filter.mp hf
      refine Finset.mem_sdiff.mpr ⟨hfF, ?_⟩
      rw [Finset.mem_singleton]
      intro hfe
      -- `f = e` 且 `f` 的两端都在 `S₁`，故 `b ∈ S₁` —— 与割边性矛盾
      rw [hfe] at h1
      exact not_mem_sideOf_b (I := I) (S := S) (a := a) (b := b) hbridge
        (h1 b (Sym2.mem_iff.mpr (Or.inr rfl)))
    · obtain ⟨hfF, h2⟩ := Finset.mem_filter.mp hf
      refine Finset.mem_sdiff.mpr ⟨hfF, ?_⟩
      rw [Finset.mem_singleton]
      intro hfe
      -- `f = e` 且 `f` 的两端都不在 `S₁`，故 `a ∉ S₁` —— 与 `a ∈ S₁` 矛盾
      rw [hfe] at h2
      exact h2 a (Sym2.mem_iff.mpr (Or.inl rfl)) (mem_sideOf_self haS)

/-! ##### ★ 和的劈分：把 `connSum I S` 按割边 `e` 拆成两半之和

**第一步（集合层）**：任意 `F ⊆ E(S)` 且 `e ∈ F`，写 `F = {e} ⊔ (F ∖ {e})`，
而 `F ∖ {e} = F₁ ⊔ F₂`（`mem_filter_sideOf_of_mem_sdiff`，其中
`F₁ := F.filter (两端在 S₁)`、`F₂ := F.filter (两端不在 S₁)`）。

**第二步（和层）**：`connSum I S` 是 `(E(S)).powerset` 上的和。把 `e` 分离出来：

> `Σ_{F ⊆ E(S)} f(F) = Σ_{F' ⊆ E(S)∖{e}} f(F' ∪ {e}) + Σ_{F' ⊆ E(S)∖{e}} f(F')`

（`e ∈ E(S)` 时 `powerset` 按"含 `e`/不含 `e`"劈开）。 -/

/-- **`powerset` 按含 `e` / 不含 `e` 劈开**（无条件成立）。 -/
theorem powerset_eq_filter_insert {α : Type*} [DecidableEq α] {s : Finset α} {e : α} :
    s.powerset = (s.powerset.filter (fun t => e ∈ t))
      ∪ (s.powerset.filter (fun t => e ∉ t)) := by
  ext t
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : e ∈ t
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, h⟩
  · rintro (⟨ht, -⟩ | ⟨ht, -⟩)
    · exact ht
    · exact ht

/-- **不含 `e` 的子集含于 `E(S) ∖ {e}`**（`e ∈ E(S)` 时）。 -/
theorem subset_sdiff_of_not_mem {α : Type*} [DecidableEq α] {s t : Finset α} {e : α}
    (ht : t ⊆ s) (hne : e ∉ t) : t ⊆ s \ {e} := by
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨ht hx, fun h => hne (Finset.mem_singleton.mp h ▸ hx)⟩

/-! ##### 装配最后一块：**和的劈分**（未证；卡点已定位到数学层）

要把 `connSum I S = − connSum I S₁ · connSum I S₂` 证出来，还差一步：

> **`edgeWithin_sdiff_eq_union`**：`E(S) ∖ {e} = E(S₁) ⊔ E(S₂)`（`S₁ := sideOf I S e a`、`S₂ := S ∖ S₁`）

**⚠️ 本轮实质发现（修正了先前对这一段的设想）**：
先前打算走 `edgeWithin_union_eq`（"无跨界边 ⇒ `E(A ∪ B) = E(A) ∪ E(B)`"）
+ `sideOf_union_sdiff`，直接得到 `E(S) = E(S₁) ∪ E(S₂)`。**这条路在数学上不成立**：
割边 `e = s(a,b)` 的两端恰好一在 `S₁`（`mem_sideOf_self`）、一在 `S₂`（`not_mem_sideOf_b`），
即 `e` **本身就是**一条跨 `S₁`/`S₂` 的 `I`-边。因此正确分解只能是

> `E(S₁) ∪ E(S₂) ∪ {e} = E(S)`（三者两两不交），等价地 `E(S) ∖ {e} = E(S₁) ⊔ E(S₂)`。

覆盖面仍然由 `not_cross_of_mem_of_connected` 提供（`f ∈ E(S)`、`f ≠ e` ⇒ 两端同侧），
**它才是**这一段的核心；`edgeWithin_union_eq` 的"无跨边"假设用不上，
需要的是"跨边只能是 `e`"这条排除性结论的 `Finset` 层形态。

**下一步的具体形态**（`edgeWithin` 成员展开的写法本轮已确认可行：
`intro e; simp only [edgeWithin, Finset.mem_filter]`，见 `edgeWithin_eq_filter`；
`rw [Finset.mem_filter]` 会失败）：

1. `edgeWithin I S = edgeWithin I S₁ ∪ edgeWithin I S₂ ∪ {e}` ——
   `⊆`：`f = e` 走 `{e}` 支；`f ≠ e` 走 `not_cross_of_mem_of_connected` 取同侧，
   再由 `mem_of_mem_edgeWithin` 把两端按侧装回 `edgeWithin I Sᵢ`；
   `⊇`：`edgeWithin_mono`（`Sᵢ ⊆ S`）加上 `heS`；
2. 两两不交：`Disjoint (edgeWithin I S₁) (edgeWithin I S₂)` 由 `edgeWithin_disjoint`
   （配 `Finset.disjoint_left` 与 `Finset.sdiff` 的不交性）；
   `e ∉ E(S₁)`、`e ∉ E(S₂)` 由 `not_mem_sideOf_b` 与 `mem_sideOf_self` 直接给出；
3. 于是 `E(S) ∖ {e} = E(S₁) ⊔ E(S₂)`，`F ⊆ E(S)` 且 `e ∈ F`
   （`mem_of_connected_of_isBridge`）⇒ `F = {e} ⊔ F₁ ⊔ F₂`，其中
   `F₁ := F ∩ E(S₁)`、`F₂ := F ∩ E(S₂)`；
4. 用 `Finset.sum_bij'`（或按 `F = {e} ⊔ (F∖{e})` 拆两层 `Finset.sum_union`）
   把 `connSum I S` 的和式劈开，配 `neg_one_pow_card_eq_neg_mul` 得
   `connSum I S = − connSum I S₁ · connSum I S₂`；
5. 强归纳：`|S₁| < |S|`、`|S₂| < |S|` —— 由 `b ∉ S₁`（`S₁ ⊆ S` 且 `b ∈ S`）
   与 `a ∉ S₂`（`a ∈ S₁`）分别给出。 -/

/-! ##### ★ 连通生成边集的**两半分解**（和之劈分第二步）

设 `e = s(a,b)` 是 `E(S)` 的割边、`S₁ := sideOf I S e a`、`S₂ := S ∖ S₁`。
若 `F ⊆ E(S)` 在 `S` 上连通生成，则 `e ∈ F`（`mem_of_connected_of_isBridge`），
于是由 `mem_filter_sideOf_of_mem_sdiff`：

> `F = {e} ⊔ (F.filter 两端在 S₁) ⊔ (F.filter 两端不在 S₁)`

且由 `connected_induce_filter_sideOf`（双侧各一次）**两半各自在自己那侧连通生成**。 -/

/-- **★ `F` 的两半分解**：`e ∈ F` ⇒ `F` 是 `{e}` 与两个 `filter` 半的不交并。

（只需 `e ∈ F` 与 `F ⊆ E(S)`：`f = e` 时 `f ∈ {e}`，`f ≠ e` 时由
`not_cross_of_mem_of_connected` 必落两半之一。**不需要**割边性或 `a ∈ S`。） -/
theorem eq_singleton_union_filter_sideOf {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V} (hF : F ⊆ edgeWithin I S)
    (heF : s(a, b) ∈ F) :
    {s(a, b)}
      ∪ (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a))
      ∪ (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) = F := by
  ext f
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ((rfl | ⟨hfF, -⟩) | ⟨hfF, -⟩)
    · exact heF
    · exact hfF
    · exact hfF
  · intro hfF
    by_cases hfe : f = s(a, b)
    · exact Or.inl (Or.inl hfe)
    · rcases not_cross_of_mem_of_connected (e := s(a, b)) (a := a) (hF hfF) hfe with h | h
      · exact Or.inl (Or.inr ⟨hfF, h⟩)
      · exact Or.inr ⟨hfF, h⟩

/-! ##### ★ 连通性对"含 `e`"的依赖（和之劈分的过滤步）

`connSum I S` 的每项带指示子 `[F 在 S 上连通生成]`。割边 `e` 的**关键作用**是：

> `F ⊆ E(S)` 连通生成 ⇒ `e ∈ F`（`mem_of_connected_of_isBridge`）

于是不含 `e` 的 `F` 贡献 `0`，可以把和限制到 `e ∈ F` 的那些子集上。 -/

omit [LinearOrder V] in
/-- **不含 `e` 的子集贡献 `0`**：`F ⊆ E(S)`、`e ∉ F` ⇒ `F` 在 `S` 上不连通。 -/
theorem not_connected_of_not_mem_bridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V}
    (heS : s(a, b) ∈ edgeWithin I S) (hF : F ⊆ edgeWithin I S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) (heF : s(a, b) ∉ F) :
    ¬ ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected :=
  fun hconn => heF (mem_of_connected_of_isBridge heS hF hconn hbridge)

/-! ##### ★★ 和的劈分（本步的核心）

**目标**：`connSum I S = − connSum I S₁ · connSum I S₂`。

**路线**（三层，每层都用已证的部件）：

1. **限制到含 `e`**：不含 `e` 的 `F` 不连通（`not_connected_of_not_mem_bridge`），
   其贡献为 `0` ⇒ 和式只需遍历 `(E(S)).powerset.filter (· ∈ ·)` 中含 `e` 的部分；
2. **分解**：含 `e` 的 `F` 写成 `{e} ⊔ F₁ ⊔ F₂`（`eq_singleton_union_filter_sideOf`），
   且 `F₁ ⊆ E(S₁)`、`F₂ ⊆ E(S₂)`；
3. **重指标 + 符号**：`F₁`、`F₂` 在 `(E(S₁)).powerset × (E(S₂)).powerset` 中独立遍历，
   符号由 `neg_one_pow_card_eq_neg_mul` 分离，连通性由双射（`connected_induce_*` /
   `connected_union_bridge`）双向保持。

**本步已落地的部分**：第 1 步（`not_connected_of_not_mem_bridge`）与第 2 步的
集合层（`eq_singleton_union_filter_sideOf`）。 -/

/-- **★ 和式限制到含割边的子集**：不含 `e` 的项为 `0`，故可把 `powerset` 过滤成
"含 `e`"而和不变。 -/
theorem connSum_eq_sum_filter_mem_bridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (heS : s(a, b) ∈ edgeWithin I S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    connSum I S
      = ∑ F ∈ (edgeWithin I S).powerset.filter (fun F => s(a, b) ∈ F),
          ite (((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected)
            ((-1 : ℤ) ^ F.card) 0 := by
  rw [connSum]
  refine (Finset.sum_subset ?_ ?_).symm
  · -- `filter ⊆ powerset`
    intro F hF
    exact (Finset.mem_filter.mp hF).1
  · -- 掉出去的项：`F ∈ powerset` 但 `e ∉ F` ⇒ 不连通 ⇒ `ite` 取 `0`
    intro F hF hnot
    have hsub : F ⊆ edgeWithin I S := Finset.mem_powerset.mp hF
    have hmem : s(a, b) ∉ F := fun h => hnot (Finset.mem_filter.mpr ⟨hF, h⟩)
    exact ite_eq_right (not_connected_of_not_mem_bridge heS hsub hbridge hmem)

omit [LinearOrder V] in
/-- **★ 两半落在各自的边集里**：`F ⊆ E(S)` 时，
`F.filter (两端在 S₁)` 的两端都在 `S₁`，故它是 `E(S₁)` 的子集（另一半同理）。 -/
theorem filter_sideOf_subset_edgeWithin {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {e : Sym2 V} {a : V}
    (hF : F ⊆ edgeWithin I S) :
    F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S e a) ⊆ edgeWithin I (sideOf I S e a) := by
  intro f hf
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hF (Finset.mem_filter.mp hf).1)).1,
    (Finset.mem_filter.mp hf).2⟩

/-! ##### ★ 重指标：`{F ∋ e}` 与"两半对"的双射

记 `S₁ := sideOf I S (s(a,b)) a`、`S₂ := S ∖ S₁`。对 `F ⊆ E(S)`、`e ∈ F` 定义

> `Φ(F) := (F ∩ E(S₁), F ∩ E(S₂))`

（注意 `F ∩ E(Sᵢ) = F.filter (两端在 Sᵢ)`，由 `eq_singleton_union_filter_sideOf`
知 `F = {e} ⊔ Φ(F).1 ⊔ Φ(F).2`，故 `Φ` 是**单射**。

反向：给定 `F₁ ⊆ E(S₁)`、`F₂ ⊆ E(S₂)`，令 `F := F₁ ∪ F₂ ∪ {e}`，
则 `Φ(F) = (F₁, F₂)` 且 `F` 的两半恰是 `F₁`、`F₂`（因两者不交且各自落位）。

连通性在双射下**双向保持**：正向 `connected_induce_filter_sideOf[_b]`、
反向 `connected_union_bridge`。 -/

/-- **★ 两半复原 `F`**：`F₁ := F.filter (两端在 S₁)`、`F₂ := F.filter (两端不在 S₁)` 时
`F₁ ∪ F₂ ∪ {e} = F`（即 `Φ` 的左逆）。

（结合方向取 **`(F₁ ∪ F₂) ∪ {e}`**，与 `Finset.union_assoc` 的默认右结合不同 ——
这里刻意选左结合，使 `F ⊆ E(S)` 下的 `filter` 恢复式直接可用。） -/
theorem union_filter_sideOf_eq {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V} (hF : F ⊆ edgeWithin I S)
    (heF : s(a, b) ∈ F) :
    {s(a, b)}
      ∪ (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a))
      ∪ (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) = F :=
  eq_singleton_union_filter_sideOf hF heF

/-- **★ `Φ` 的右逆**：若 `F₁ ⊆ E(S₁)`、`F₂ ⊆ E(S₂)`（`S₂ := S ∖ S₁`），
令 `F := F₁ ∪ F₂ ∪ {e}`，则 `F` 的两个 `filter` 半**分别**是 `F₁`、`F₂`。

（关键：`F₁` 的边两端都在 `S₁`；`F₂` 的边两端都不在 `S₁`（因在 `S ∖ S₁` 内）；
`e` 的两端一在 `S₁`（`a`）一不在（`b`）。故三块的谓词互不相同。） -/
theorem filter_union_filter_eq_of_subset {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S S₁ : Finset V} {F₁' F₂' : Finset (Sym2 V)} {a b : V}
    (hS₁ : S₁ = sideOf I S (s(a, b)) a)
    (haS₁ : a ∈ S₁) (hbS₂ : b ∈ S \ S₁)
    (hF₁ : F₁' ⊆ edgeWithin I S₁) (hF₂ : F₂' ⊆ edgeWithin I (S \ S₁)) :
    ((F₁' ∪ F₂' ∪ {s(a, b)}).filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a) = F₁')
      ∧ ((F₁' ∪ F₂' ∪ {s(a, b)}).filter
          (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a) = F₂') := by
  subst hS₁
  constructor
  · refine Finset.Subset.antisymm ?_ ?_
    · intro f hf
      have hf2 : f ∈ F₁' ∪ F₂' ∪ {s(a, b)} := (Finset.mem_filter.mp hf).1
      have hpred := (Finset.mem_filter.mp hf).2
      rcases Finset.mem_union.mp hf2 with hf2 | hf2
      · rcases Finset.mem_union.mp hf2 with hf2 | hf2
        · exact hf2
        · -- `f ∈ F₂' ⊆ E(S∖S₁)` ⇒ 两端 ∉ `S₁`，与 `hpred` 矛盾
          exfalso
          revert hpred hf2
          refine Sym2.ind (fun x y => ?_) f
          intro hpred hf2
          exact (Finset.mem_sdiff.mp (mem_of_mem_edgeWithin (hF₂ hf2) x
            (Sym2.mem_iff.mpr (Or.inl rfl)))).2 (hpred x (Sym2.mem_iff.mpr (Or.inl rfl)))
      · -- `f = e` ⇒ `b ∈ S₁`，与 `hbS₂` 矛盾
        exfalso
        rw [Finset.mem_singleton] at hf2
        revert hpred
        rw [hf2]
        intro hpred
        exact (Finset.mem_sdiff.mp hbS₂).2 (hpred b (Sym2.mem_iff.mpr (Or.inr rfl)))
    · intro f hf
      refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hf), ?_⟩
      exact mem_of_mem_edgeWithin (hF₁ hf)
  · refine Finset.Subset.antisymm ?_ ?_
    · intro f hf
      have hf2 : f ∈ F₁' ∪ F₂' ∪ {s(a, b)} := (Finset.mem_filter.mp hf).1
      have hpred := (Finset.mem_filter.mp hf).2
      rcases Finset.mem_union.mp hf2 with hf2 | hf2
      · rcases Finset.mem_union.mp hf2 with hf2 | hf2
        · -- `f ∈ F₁' ⊆ E(S₁)` ⇒ 两端 ∈ `S₁`，与 `hpred` 矛盾
          exfalso
          revert hpred hf2
          refine Sym2.ind (fun x y => ?_) f
          intro hpred hf2
          exact hpred x (Sym2.mem_iff.mpr (Or.inl rfl))
            (mem_of_mem_edgeWithin (hF₁ hf2) x (Sym2.mem_iff.mpr (Or.inl rfl)))
        · exact hf2
      · -- `f = e` ⇒ `a ∉ S₁`，与 `haS₁` 矛盾
        exfalso
        rw [Finset.mem_singleton] at hf2
        revert hpred
        rw [hf2]
        intro hpred
        exact hpred a (Sym2.mem_iff.mpr (Or.inl rfl)) haS₁
    · intro f hf
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hf), ?_⟩
      intro v hv
      exact (Finset.mem_sdiff.mp (mem_of_mem_edgeWithin (hF₂ hf) v hv)).2

/-! ##### ★★ 和的劈分：`connSum I S = − connSum I S₁ · connSum I S₂`

**逐项形态**（本段的起点）：设 `S₁ := sideOf I S (s(a,b)) a`、`S₂ := S ∖ S₁`，
`F ⊆ E(S)` 且 `e := s(a,b) ∈ F`，记 `F₁ := F.filter (两端在 S₁)`、
`F₂ := F.filter (两端在 S₂)`（即"不在 `S₁`"那一半）。则

* `F = {e} ⊔ F₁ ⊔ F₂`（`eq_singleton_union_filter_sideOf`）；
* `F₁ ⊆ E(S₁)`、`F₂ ⊆ E(S₂)`（`filter_sideOf_subset_edgeWithin`）；
* `F` 在 `S` 上连通生成 ⟺ `F₁` 在 `S₁` 上连通生成 **且** `F₂` 在 `S₂` 上连通生成
  （正向 `connected_induce_filter_sideOf[_b]`、反向 `connected_union_bridge`）；
* `(−1)^{|F|} = −(−1)^{|F₁|}·(−1)^{|F₂|}`（`neg_one_pow_card_eq_neg_mul`）。

于是逐项 `ite` 可写成"两个 `ite` 之积再乘 `−1`"，整体即得因子化。 -/

/-- **★ 记号的落地**：把 `F.filter (两端在 S₂)` 与 `S₂ := S ∖ S₁` 对齐，
给出与 `filter_sideOf_subset_edgeWithin` 同型的子集结论。 -/
theorem filter_sdiff_sideOf_subset_edgeWithin {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {e : Sym2 V} {a : V}
    (hF : F ⊆ edgeWithin I S) :
    F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S e a)
      ⊆ edgeWithin I (S \ sideOf I S e a) := by
  intro f hf
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hF (Finset.mem_filter.mp hf).1)).1,
    fun v hv => Finset.mem_sdiff.mpr
      ⟨mem_of_mem_edgeWithin (hF (Finset.mem_filter.mp hf).1) v hv,
       (Finset.mem_filter.mp hf).2 v hv⟩⟩

/-! ##### ★ `b` 那侧 ⊆ `a` 侧的补集（重指标所需的方向）

`e = s(a,b)` 是 `E(S)` 的割边时，删边图里 `a`、`b` 不可达
（`not_reachable_of_isBridge`）。由 `sideOf_of_mem_edge`：删边图中每一步都不跨侧，
故删边图里与 `b` 可达的顶点**都不在 `a` 侧**。

这就是把 `connected_induce_filter_sideOf_b` 的结论
（`b` 那侧 `sideOf I S e b` 上连通）搬到重指标所需的
`S ∖ sideOf I S e a` 形状上所需要的**唯一**集合事实。 -/

/-- **★ `b` 那侧 ⊆ `a` 侧的补集**（`e` 是割边时）：`sideOf I S e b ⊆ S \ sideOf I S e a`。

若 `x` 同时与 `b`、与 `a` 在删边图中可达，则 `a`、`b` 在删边图中可达
—— 与 `e = s(a,b)` 是割边矛盾。 -/
theorem sideOf_b_subset_sdiff_sideOf_a {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    sideOf I S (s(a, b)) b ⊆ S \ sideOf I S (s(a, b)) a := by
  intro x hx
  have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
  have hxb : ((edgeGraph I S).deleteEdges {s(a, b)}).Reachable b x :=
    (Finset.mem_filter.mp hx).2
  refine Finset.mem_sdiff.mpr ⟨hxS, ?_⟩
  intro hx₁
  have hax : ((edgeGraph I S).deleteEdges {s(a, b)}).Reachable a x :=
    (Finset.mem_filter.mp hx₁).2
  exact absurd (hax.trans hxb.symm)
    (not_reachable_of_isBridge (G := edgeGraph I S) hbridge)

/-- **★ `a` 侧 ⊆ `b` 侧的补集**：`sideOf I S e a ⊆ S \ sideOf I S e b`（对称版）。 -/
theorem sideOf_a_subset_sdiff_sideOf_b {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    sideOf I S (s(a, b)) a ⊆ S \ sideOf I S (s(a, b)) b := by
  have hswap : (s(b, a) : Sym2 V) = s(a, b) := Sym2.eq_swap
  have hbridge' : (edgeGraph I S).IsBridge s(b, a) := by rw [hswap]; exact hbridge
  have h := sideOf_b_subset_sdiff_sideOf_a (I := I) (S := S) (a := b) (b := a) hbridge'
  rwa [hswap] at h

/-! ##### ★ 反包含：`S ∖ sideOf a ⊆ sideOf b`（需 `S` 在 `E(S)` 上连通）

**不切分走步的路线**：对 `G := edgeGraph I S` 上从 `a` 出发的走步做归纳，携带不变量

> 终点 `z` 满足：`z ∈ sideOf I S e a` **或** `z` 在删边图中与 `b` 可达。

* `nil`：起点 `a ∈ S₁`，成立；
* 一步 `z — z'`（边 `f`）：
  - 若 `f ≠ e`：由 `sideOf_step_same`，`z' ∈ S₁ ↔ z ∈ S₁`；
    且 `f` 在删边图里可用 ⇒ 可达性也沿这一步传递（两侧都不影响另一支）；
  - 若 `f = e`：则 `{z,z'} = {a,b}`，两端交换 —— `z ∈ S₁` 时 `z' = b` 或 `a`，
    前者落在"与 `b` 可达（自反）"支，后者 `a ∈ S₁` 仍在第一支。

**用一个更强的、两支都平凡的陈述**可以省掉这个两难：
直接证"**若走步避开了 `e`**，则终点与起点同侧"（这就是已有的
`reachable_filter_of_walk_aux` 的形态）。故真正的证明只需处理"走步是否用到 `e`"。
下轮用 `List.count` 奇偶性（`count_bridge_even_iff_same_side`）统一处理：
路径用 `e` 偶数次 ⇒ 同侧；而**路径**（`IsPath`）里 `e` 至多一次 ⇒ 用 `e` ⟺ 两端异侧。 -/

omit [LinearOrder V] in
/-- **★ `b` 侧的可达性刻画**：`x ∈ S` 且 `x` 与 `b` 在 `G.deleteEdges {e}` 中可达
⟺ `x ∈ sideOf I S e b`（定义即此，供调用方免于展开 `sideOf`）。 -/
theorem mem_sideOf_iff_reachable {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {e : Sym2 V} {b x : V} :
    x ∈ sideOf I S e b ↔
      x ∈ S ∧ ((edgeGraph I S).deleteEdges {e}).Reachable b x :=
  Finset.mem_filter

omit [LinearOrder V] in
/-- **★ 一侧保侧（`b` 侧版）**：`x ∈ sideOf I S e b`、`s(x,y) ∈ F ⊆ E(S)`、`s(x,y) ≠ e`
⇒ `y ∈ sideOf I S e b`。

与 `sideOf_of_mem_edge` 同型，只是基点取 `b`；直接调用 `sideOf_of_mem_edge` 的
`a := b`、`b := a` 版本，两侧的 `sideOf I S (s(a,b))` 与 `sideOf I S (s(b,a))`
由 `Sym2.eq_swap` 统一。 -/
theorem sideOf_b_of_mem_edge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b x y : V}
    (hF : F ⊆ edgeWithin I S)
    (hxy : (s(x, y) : Sym2 V) ∈ F) (hne : (s(x, y) : Sym2 V) ≠ s(a, b))
    (hx : x ∈ sideOf I S (s(a, b)) b) :
    y ∈ sideOf I S (s(a, b)) b := by
  have hswap : (s(b, a) : Sym2 V) = s(a, b) := Sym2.eq_swap
  have hne' : (s(x, y) : Sym2 V) ≠ s(b, a) := fun h => hne (h.trans hswap)
  -- 目标里 `sideOf` 的边是 `s(b,a)`；`hx` 用的是 `s(a,b)`，故把 `hx` 改写成 `s(b,a)`
  have hx' : x ∈ sideOf I S (s(b, a)) b := by rw [hswap]; exact hx
  have h := sideOf_of_mem_edge (I := I) (S := S) (F := F) (a := b) (b := a)
    hF hxy hne' hx'
  rw [hswap] at h
  exact h

/-- **★★ 反包含：`S ∖ sideOf a ⊆ sideOf b`**（需 `S` 在 `E(S)` 上连通）。

对 `E(S)` 上从 `a` 出发的走步归纳，不变量

> 终点 `z`：`z ∈ sideOf I S e a` **或** `z ∈ sideOf I S e b`。

* 起点 `a`：`a ∈ S₁`（`mem_sideOf_self`）；
* 一步 `z — z'`（边 `f`）：
  - `f ≠ e`：`z ∈ S₁ ⇒ z' ∈ S₁`（`sideOf_of_mem_edge`），
    `z ∈ S_b ⇒ z' ∈ S_b`（同一引理对 `b` 的版本，由 `Sym2.eq_swap`）；
  - `f = e`：`{z,z'} = {a,b}` ⇒ 两支互换，仍落在两支之一。

（此不变量比"同侧"弱、比"可达"强，正好让两个分支都封口。
**不需要割边性** —— 这里只用到 `e ∈ E(S)`，故签名里不出现 `IsBridge`。） -/
theorem mem_sideOf_a_or_mem_sideOf_b_of_reachable {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (haS : a ∈ S)
    {z : V} (hz : (edgeGraph I S).Reachable a z) :
    z ∈ sideOf I S (s(a, b)) a ∨ z ∈ sideOf I S (s(a, b)) b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hz
  induction hz with
  | refl => exact Or.inl (mem_sideOf_self haS)
  | tail _ hadj ih =>
    rename_i u v _
    -- `hadj : (edgeGraph I S).Adj u v`；`ih : u ∈ S₁ ∨ u ∈ S_b`
    rw [edgeGraph, SimpleGraph.fromEdgeSet_adj] at hadj
    by_cases hEq : (s(u, v) : Sym2 V) = s(a, b)
    · -- 这一步就是 `e`：`{u,v} = {a,b}`，故 `v ∈ S₁` 或 `v ∈ S_b`
      have hvmem : v ∈ s(a, b) := hEq ▸ (Sym2.mem_iff.mpr (Or.inr rfl) : v ∈ s(u, v))
      rcases Sym2.mem_iff.mp hvmem with hva | hvb
      · -- `v = a` ⇒ `v ∈ S₁`
        left
        rw [hva]
        exact mem_sideOf_self haS
      · -- `v = b` ⇒ `v ∈ S_b`（自反可达）
        right
        refine Finset.mem_filter.mpr ⟨mem_of_mem_edgeWithin hadj.1 v
          (Sym2.mem_iff.mpr (Or.inr rfl)), ?_⟩
        rw [hvb]
    · -- 这一步不是 `e`：两侧各自保侧
      rcases ih with h | h
      · left
        exact sideOf_of_mem_edge (F := edgeWithin I S) (fun _ hh => hh) hadj.1 hEq h
      · right
        exact sideOf_b_of_mem_edge (F := edgeWithin I S) (fun _ hh => hh) hadj.1 hEq h

/-- **★★ 反包含：`S ∖ sideOf a ⊆ sideOf b`**（需 `S` 在 `E(S)` 上连通）。

由 `mem_sideOf_a_or_mem_sideOf_b_of_reachable`：只需"`a` 能到达 `S` 内每个点"
（比 `Connected` 弱，且正是 `F` 的连通生成性所直接提供的）。 -/
theorem sdiff_sideOf_a_subset_sideOf_b {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (haS : a ∈ S)
    (hconn : ∀ x ∈ S, (edgeGraph I S).Reachable a x) :
    S \ sideOf I S (s(a, b)) a ⊆ sideOf I S (s(a, b)) b := by
  intro x hx
  obtain ⟨hxS, hxnot⟩ := Finset.mem_sdiff.mp hx
  rcases mem_sideOf_a_or_mem_sideOf_b_of_reachable (I := I) (S := S) (a := a) (b := b)
    haS (hconn x hxS) with h | h
  · exact absurd h hxnot
  · exact h

/-- **★★ 两侧互补**：`a ∈ S`、`a` 在 `E(S)` 上能到达 `S` 内每个点
⇒ `sideOf I S e a ∪ sideOf I S e b = S`。

两向：`⊆` 由 `sideOf_subset`；`⊇` 由 `S ∖ S₁ ⊆ S_b`（反包含）与
`S₁ ∪ (S ∖ S₁) = S`（`sideOf_union_sdiff`）。 -/
theorem sideOf_union_sideOf_eq {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (haS : a ∈ S)
    (hconn : ∀ x ∈ S, (edgeGraph I S).Reachable a x) :
    sideOf I S (s(a, b)) a ∪ sideOf I S (s(a, b)) b = S := by
  refine Finset.Subset.antisymm ?_ ?_
  · -- `S₁ ⊆ S` 且 `S_b ⊆ S ∖ S₁ ⊆ S`
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact sideOf_subset h
    · exact sideOf_subset h
  · intro x hx
    by_cases hx₁ : x ∈ sideOf I S (s(a, b)) a
    · exact Finset.mem_union_left _ hx₁
    · exact Finset.mem_union_right _
        (sdiff_sideOf_a_subset_sideOf_b (I := I) (S := S) (a := a) (b := b) haS hconn
          (Finset.mem_sdiff.mpr ⟨hx, hx₁⟩))

/-! ##### ★★ 连通性双向搬运（重指标的作用域层）

有了 `sideOf_union_sideOf_eq`，`connected_induce_filter_sideOf_b` 的结论
（`b` 那侧上连通）可以换到重指标真正需要的 `S ∖ S₁` 形状。

* **正向**：`F` 在 `S` 上连通生成 ⇒ `F₁` 在 `S₁` 上连通、`F₂` 在 `S ∖ S₁` 上连通；
* **反向**：两半各自连通、`e ∈ F` ⇒ `F` 连通。 -/

/-- **★★ 两侧互补（集合等式）**：`a ∈ S`、`a` 能到达 `S` 内每个点、`e = s(a,b)` 是割边
⇒ **`S ∖ sideOf I S e a = sideOf I S e b`**（把 `connected_induce_filter_sideOf_b`
的 `b` 侧口径换到重指标所需的 `S ∖ S₁` 形状）。

两向：`⊆` 由 `sdiff_sideOf_a_subset_sideOf_b`；`⊇` 由 `sideOf_b_subset_sdiff_sideOf_a`。 -/
theorem sdiff_sideOf_a_eq_sideOf_b {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (haS : a ∈ S)
    (hconn : ∀ x ∈ S, (edgeGraph I S).Reachable a x)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    S \ sideOf I S (s(a, b)) a = sideOf I S (s(a, b)) b :=
  Finset.Subset.antisymm (sdiff_sideOf_a_subset_sideOf_b haS hconn)
    (sideOf_b_subset_sdiff_sideOf_a hbridge)

omit [LinearOrder V] in
/-- **★ `F` 在 `S` 上连通生成 ⇒ `S` 在 `E(S)` 上连通**（重指标所需的辅助事实）。

注意 `edgeGraph I S` 作为**整张 `V` 上的图**未必连通（`S` 外的顶点是孤立点），
故这里陈述的是 `S` 上**诱导图**的连通性 —— 与 `connected_induce_filter_sideOf`
所用口径一致。 -/
theorem connected_induce_edgeGraph_of_connected {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} (hF : F ⊆ edgeWithin I S)
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    ((edgeGraph I S).induce (↑S : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨m, hm⟩ := hconn.nonempty
  refine ⟨⟨m, hm⟩, fun w => ?_⟩
  -- `hconn` 的走步在 `(fromEdgeSet F).induce ↑S` 上；目标图是 `(edgeGraph I S).induce ↑S`。
  -- 两者顶点类型同为 `↥S`，用 `Reachable.mono` 沿图的包含提升（`fromEdgeSet F ≤ edgeGraph I S`）。
  refine SimpleGraph.Reachable.mono ?_ (hconn ⟨m, hm⟩ w)
  intro x y hxy
  rw [SimpleGraph.induce_adj] at hxy
  rw [SimpleGraph.induce_adj]
  rw [SimpleGraph.fromEdgeSet_adj] at hxy
  rw [edgeGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨hF hxy.1, hxy.2⟩

set_option maxHeartbeats 2000000 in
/-- **★ 正向搬运**：`F` 在 `S` 上连通生成 ⇒ 两个 `filter` 半各自在自己那侧连通生成
（第二半的口径是 `S ∖ S₁`，由 `sdiff_sideOf_a_eq_sideOf_b` 与
`connected_induce_filter_sideOf_b` 拼出）。 -/
theorem connected_filter_sideOf_of_connected {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V}
    (heS : s(a, b) ∈ edgeWithin I S) (haS : a ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) (hF : F ⊆ edgeWithin I S)
    (hconn : ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected) :
    (((SimpleGraph.fromEdgeSet
          (↑(F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)) : Set (Sym2 V))).induce
            (↑(sideOf I S (s(a, b)) a) : Set V)).Connected
      ∧ ((SimpleGraph.fromEdgeSet
          (↑(F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) : Set (Sym2 V))).induce
            (↑(S \ sideOf I S (s(a, b)) a) : Set V)).Connected) := by
  have hbS : b ∈ S := mem_of_mem_edgeWithin heS b (Sym2.mem_iff.mpr (Or.inr rfl))
  refine ⟨connected_induce_filter_sideOf (q := b) haS hF hbridge hconn, ?_⟩
  -- 由诱导连通性得"`a` 能到达 `S` 内每点"，再取集合等式把 `b` 侧口径换成 `S ∖ S₁`
  have hreach : ∀ x ∈ S, (edgeGraph I S).Reachable a x := by
    intro x hxS
    obtain ⟨p⟩ := hconn ⟨a, haS⟩ ⟨x, hxS⟩
    exact ⟨(p.map (SimpleGraph.Embedding.induce (↑S : Set V)).toHom).mapLe (by
      intro u v huv
      rw [SimpleGraph.fromEdgeSet_adj] at huv
      rw [edgeGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨hF huv.1, huv.2⟩)⟩
  have heq := sdiff_sideOf_a_eq_sideOf_b (I := I) (S := S) (a := a) (b := b)
    haS hreach hbridge
  -- 两个 `filter` 的谓词只差在集合 `sideOf b` 与 `S ∖ sideOf a` 上；由 `heq` 相同
  -- 两个 `filter` 的谓词在 `F ⊆ E(S)` 上等价（端点都在 `S` 内），故两个 `filter` 相等
  have hfilt : F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) b)
      = F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a) := by
    refine Finset.filter_congr fun f hfF => ?_
    have hfS : ∀ x ∈ f, x ∈ S := mem_of_mem_edgeWithin (hF hfF)
    constructor
    · intro h x hx
      exact (Finset.mem_sdiff.mp (heq ▸ h x hx)).2
    · intro h x hx
      rw [← heq]
      exact Finset.mem_sdiff.mpr ⟨hfS x hx, fun hx₁ => h x hx hx₁⟩
  rw [← hfilt, heq]
  exact connected_induce_filter_sideOf_b (a := a) hbS hF hbridge hconn

/-! ##### ★★ 逐项恒等式（和之劈分的代数核心）

对 `F ⊆ E(S)`、`e ∈ F`，两个 `filter` 半 `F₁`、`F₂` 满足

> `[F 连通]·(−1)^{|F|} = −([F₁ 连通]·(−1)^{|F₁|})·([F₂ 连通]·(−1)^{|F₂|})`

（连通性双向等价由 `connected_filter_sideOf_of_connected` / `connected_union_bridge`；
符号由 `card_eq_card_filter_add_card_filter_add_one` + `neg_one_pow_card_eq_neg_mul`。）
这就是把 `connSum I S` 的每一项与 `connSum I S₁ · connSum I S₂` 的对应项联系起来的桥。 -/

set_option maxHeartbeats 2000000 in
set_option maxHeartbeats 2000000 in
/-- **★ 反向搬运**：`e ∈ F`、两半各自在自己那侧连通生成 ⇒ `F` 在 `S` 上连通生成。

由 `connected_union_bridge` 给出 `F₁ ∪ F₂ ∪ {e}` 的连通性，
再用 `union_filter_sideOf_eq`（需 `e ∈ F`）把并换回 `F`。 -/
theorem connected_of_connected_filter_sideOf {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V}
    (heS : s(a, b) ∈ edgeWithin I S) (haS : a ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) (hF : F ⊆ edgeWithin I S)
    (heF : s(a, b) ∈ F)
    (hc₁ : ((SimpleGraph.fromEdgeSet
          (↑(F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)) : Set (Sym2 V))).induce
            (↑(sideOf I S (s(a, b)) a) : Set V)).Connected)
    (hc₂ : ((SimpleGraph.fromEdgeSet
          (↑(F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) : Set (Sym2 V))).induce
            (↑(S \ sideOf I S (s(a, b)) a) : Set V)).Connected) :
    ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected := by
  have hbS : b ∈ S := mem_of_mem_edgeWithin heS b (Sym2.mem_iff.mpr (Or.inr rfl))
  have haS₁ : a ∈ sideOf I S (s(a, b)) a := mem_sideOf_self haS
  have hbS₂ : b ∈ S \ sideOf I S (s(a, b)) a :=
    Finset.mem_sdiff.mpr ⟨hbS, not_mem_sideOf_b hbridge⟩
  -- 把 `hc₂` 的口径从 `S ∖ S₁` 换成 `b` 侧（`connected_union_bridge` 要后者）
  have hreach : ∀ x ∈ S, (edgeGraph I S).Reachable a x := by
    intro x hxS
    by_cases hx₁ : x ∈ sideOf I S (s(a, b)) a
    · -- `x ∈ S₁`：用 `hc₁` 的连通性走到 `a`
      obtain ⟨p⟩ := hc₁ ⟨a, haS₁⟩ ⟨x, hx₁⟩
      exact ⟨(p.map (SimpleGraph.Embedding.induce _).toHom).mapLe (by
        intro u v huv
        rw [SimpleGraph.fromEdgeSet_adj] at huv
        rw [edgeGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨hF (Finset.mem_filter.mp huv.1).1, huv.2⟩)⟩
    · -- `x ∈ S ∖ S₁`：先到 `b`（`hc₂`），再走割边 `e` 到 `a`
      obtain ⟨p⟩ := hc₂ ⟨b, hbS₂⟩ ⟨x, Finset.mem_sdiff.mpr ⟨hxS, hx₁⟩⟩
      have hba : (edgeGraph I S).Reachable b x :=
        ⟨(p.map (SimpleGraph.Embedding.induce _).toHom).mapLe (by
          intro u v huv
          rw [SimpleGraph.fromEdgeSet_adj] at huv
          rw [edgeGraph, SimpleGraph.fromEdgeSet_adj]
          exact ⟨hF (Finset.mem_filter.mp huv.1).1, huv.2⟩)⟩
      -- `a — b` 是 `E(S)` 的一条边
      exact (SimpleGraph.Adj.reachable (by
        rw [edgeGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨heS, fun h => by
          have h1 : (s(a, b) : Sym2 V) ∈ I.edgeSet := by
            rw [← SimpleGraph.mem_edgeFinset]; exact (Finset.mem_filter.mp heS).1
          exact SimpleGraph.not_isDiag_of_mem_edgeSet (G := I) h1 h⟩)).trans hba
  have heq := sdiff_sideOf_a_eq_sideOf_b (I := I) (S := S) (a := a) (b := b)
    haS hreach hbridge
  -- 把 `hc₂` 的谓词与顶点集换成 `b` 侧
  have hfilt : F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) b)
      = F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a) := by
    refine Finset.filter_congr fun f hfF => ?_
    have hfS : ∀ x ∈ f, x ∈ S := mem_of_mem_edgeWithin (hF hfF)
    constructor
    · intro h x hx
      exact (Finset.mem_sdiff.mp (heq ▸ h x hx)).2
    · intro h x hx
      rw [← heq]
      exact Finset.mem_sdiff.mpr ⟨hfS x hx, fun hx₁ => h x hx hx₁⟩
  -- `connected_union_bridge` 给的是 `F₁ ∪ F₂ ∪ {e}` 上的连通性；
  -- 而 `union_filter_sideOf_eq` 给的等式左端是 `{e} ∪ F₁ ∪ F₂`。用交换律对齐。
  have hunion : ({s(a, b)}
        ∪ F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)
        ∪ F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a) : Finset (Sym2 V))
      = F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)
        ∪ F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a) ∪ {s(a, b)} := by
    ext f
    simp only [Finset.mem_union, Finset.mem_singleton]
    tauto
  have h := connected_union_bridge (e := s(a, b)) haS₁ hbS₂ haS hbS
    sideOf_subset Finset.sdiff_subset
    (filter_sideOf_subset_edgeWithin hF) (filter_sdiff_sideOf_subset_edgeWithin hF)
    rfl hc₁ hc₂
  rw [← union_filter_sideOf_eq hF heF, hunion]
  exact h

/-- **★★ 逐项恒等式**：`F ⊆ E(S)`、`e ∈ F` 时，

> `[F 连通]·(−1)^{|F|} = −([F₁ 连通]·(−1)^{|F₁|})·([F₂ 连通]·(−1)^{|F₂|})`

其中 `F₁`、`F₂` 是 `F` 的两个 `filter` 半。

**连通性双向等价已备**（`connected_filter_sideOf_of_connected` 正向、
`connected_union_bridge` 反向），**符号恒等式已备**（`neg_one_pow_card_eq_neg_mul`）。
故本引理只是二者的机械合并：分"`F` 连通/不连通"两支，
连通时两个指示子都为真、不连通时至少一个为假（且左端为 `0`）。 -/
theorem ite_connected_mul_sign_eq_neg_mul {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V}
    (heS : s(a, b) ∈ edgeWithin I S) (haS : a ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) (hF : F ⊆ edgeWithin I S)
    (heF : s(a, b) ∈ F) :
    ite (((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected)
        ((-1 : ℤ) ^ F.card) 0
      = -((ite (((SimpleGraph.fromEdgeSet
              (↑(F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)) : Set (Sym2 V))).induce
                (↑(sideOf I S (s(a, b)) a) : Set V)).Connected)
            ((-1 : ℤ) ^ (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)).card) 0)
          * (ite (((SimpleGraph.fromEdgeSet
              (↑(F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) : Set (Sym2 V))).induce
                (↑(S \ sideOf I S (s(a, b)) a) : Set V)).Connected)
            ((-1 : ℤ) ^ (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)).card) 0)) := by
  -- 记三个连通性命题与符号
  set c := ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected
    with hc
  set c₁ := ((SimpleGraph.fromEdgeSet
      (↑(F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)) : Set (Sym2 V))).induce
        (↑(sideOf I S (s(a, b)) a) : Set V)).Connected with hc₁
  set c₂ := ((SimpleGraph.fromEdgeSet
      (↑(F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) : Set (Sym2 V))).induce
        (↑(S \ sideOf I S (s(a, b)) a) : Set V)).Connected with hc₂
  by_cases hc' : c
  · -- `F` 连通：两半各自连通（正向搬运），故两个指示子都取 `then`
    have hboth := connected_filter_sideOf_of_connected heS haS hbridge hF hc'
    rw [ite_eq_left hc', ite_eq_left (hc₁ ▸ hboth.1), ite_eq_left (hc₂ ▸ hboth.2)]
    exact neg_one_pow_card_eq_neg_mul heS haS hF hbridge hc'
  · -- `F` 不连通：左端为 `0`；右端需证至少一个指示子取 `then` 不可能同时成立
    rw [ite_eq_right hc']
    -- 若两半都连通，则由反向搬运 `F` 连通 —— 矛盾
    by_cases h₁ : c₁
    · by_cases h₂ : c₂
      · exact absurd (connected_of_connected_filter_sideOf heS haS hbridge hF heF
          (hc₁ ▸ h₁) (hc₂ ▸ h₂)) hc'
      · rw [ite_eq_left h₁, ite_eq_right h₂]; ring
    · rw [ite_eq_right h₁]; ring

/-- **★★ 右逆（对 ↦ `F` ↦ 对 是恒等）**：给定 `G₁ ⊆ E(S₁)`、`G₂ ⊆ E(S₂)`，
令 `F := G₁ ∪ G₂ ∪ {e}`，则 `(F ∩ E(S₁), F ∩ E(S₂)) = (G₁, G₂)`。

（由 `filter_union_filter_eq_of_subset`：两个 `filter` 半分别恰为 `G₁`、`G₂`。） -/
theorem filter_pair_union_eq_self {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S S₁ : Finset V} {G₁ G₂ : Finset (Sym2 V)} {a b : V}
    (hS₁ : S₁ = sideOf I S (s(a, b)) a)
    (haS₁ : a ∈ S₁) (hbS₂ : b ∈ S \ S₁)
    (hG₁ : G₁ ⊆ edgeWithin I S₁) (hG₂ : G₂ ⊆ edgeWithin I (S \ S₁)) :
    (G₁ ∪ G₂ ∪ {s(a, b)}).filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a) = G₁
      ∧ (G₁ ∪ G₂ ∪ {s(a, b)}).filter
          (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a) = G₂ :=
  filter_union_filter_eq_of_subset hS₁ haS₁ hbS₂ hG₁ hG₂

/-! ##### ★★ 双射的**左逆**（`F` ↦ 对 ↦ `F` 是恒等）

对 `F ∈ (E(S)).powerset.filter (· ∋ e)`，令
`Φ(F) := (F.filter (两端在 S₁), F.filter (两端不在 S₁))`，则
`Φ(F).1 ∪ Φ(F).2 ∪ {e} = F`（`union_filter_sideOf_eq`）——
这正是 `sum_bij'` 的 `left_inv`。 -/

/-- **★ 左逆**：`F ⊆ E(S)`、`e ∈ F` ⇒ `Φ(F)` 的两个分量与 `{e}` 拼回 `F`。

（结论的结合方向取 `(F₁ ∪ F₂) ∪ {e}`，与 `union_filter_sideOf_eq` 的
`{e} ∪ F₁ ∪ F₂` 不同 —— 用 `ext` 回避结合方向问题。） -/
theorem filter_pair_union_filter_eq_self {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {F : Finset (Sym2 V)} {a b : V} (hF : F ⊆ edgeWithin I S)
    (heF : s(a, b) ∈ F) :
    (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a))
      ∪ (F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) ∪ {s(a, b)} = F := by
  have h := union_filter_sideOf_eq hF heF
  -- `h : {e} ∪ (F₁ ∪ F₂) = F`；把整体 `{e} ∪ (F₁ ∪ F₂)` 交换成 `(F₁ ∪ F₂) ∪ {e}`
  have hcomm : ({s(a, b)} ∪ (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)
        ∪ F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)) : Finset (Sym2 V))
      = F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a)
        ∪ F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a) ∪ {s(a, b)} :=
    Finset.union_comm _ _
  rw [Finset.union_assoc] at h
  exact hcomm ▸ h

/-! ##### ★★ 和之劈分：`sum_bij'` 装配

把 `connSum I S` 的受限和式（`connSum_eq_sum_filter_mem_bridge`）的指标集
`{F ∋ e}` 换成"半对"集合 `(E(S₁)).powerset ×ˢ (E(S ∖ S₁)).powerset`：

* `toFun F := (F.filter P, F.filter ¬P)`，其中 `P x := x ∈ sideOf I S e a`；
* `invFun p := p.1 ∪ p.2 ∪ {e}`；
* `left_inv` / `right_inv` 恰是第 35 段的两条互逆律
  （`filter_pair_union_filter_eq_self` / `filter_pair_union_eq_self`）。

**关键**：`invFun` 里的并形状就是两条互逆律里钉死的形状，故不会再碰到
第 35 段那种结合方向失配。 -/

/-- **★★ 重指标（集合层）**：受限和式的指标集与"半对"集合之间存在 `Finset.sum_bij'` 双射，
映射为 `F ↦ (F ∩ E(S₁), F ∩ E(S ∖ S₁))`、`(G₁,G₂) ↦ G₁ ∪ G₂ ∪ {e}`。

**`sum_bij'` 的 7 个义务顺序**（实测自 Mathlib 的 `sum_bij'` 用法）：
`toFun`、`invFun`、`toFun` 落域、`invFun` 落域、`left_inv`、`right_inv`、值一致。 -/
theorem sum_filter_mem_bridge_eq_sum_pairs {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (heS : s(a, b) ∈ edgeWithin I S) (haS : a ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b))
    (g : Finset (Sym2 V) → ℤ) :
    (∑ F ∈ (edgeWithin I S).powerset.filter (fun F => s(a, b) ∈ F), g F)
      = ∑ p ∈ (edgeWithin I (sideOf I S (s(a, b)) a)).powerset
              ×ˢ (edgeWithin I (S \ sideOf I S (s(a, b)) a)).powerset,
          g (p.1 ∪ p.2 ∪ {s(a, b)}) := by
  classical
  have hbS₂ : b ∈ S \ sideOf I S (s(a, b)) a :=
    Finset.mem_sdiff.mpr
      ⟨mem_of_mem_edgeWithin heS b (Sym2.mem_iff.mpr (Or.inr rfl)),
        not_mem_sideOf_b hbridge⟩
  refine Finset.sum_bij'
    (fun F _ => (F.filter (fun f => ∀ x ∈ f, x ∈ sideOf I S (s(a, b)) a),
        F.filter (fun f => ∀ x ∈ f, x ∉ sideOf I S (s(a, b)) a)))
    (fun p _ => p.1 ∪ p.2 ∪ {s(a, b)}) ?_ ?_ ?_ ?_ ?_
  · -- (3) `toFun` 落域：两半分别落在 `E(S₁)`、`E(S∖S₁)` 的幂集里
    intro F hF
    obtain ⟨hFpow, -⟩ := Finset.mem_filter.mp hF
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr
          (filter_sideOf_subset_edgeWithin (Finset.mem_powerset.mp hFpow)),
       Finset.mem_powerset.mpr
          (filter_sdiff_sideOf_subset_edgeWithin (Finset.mem_powerset.mp hFpow))⟩
  · -- (4) `invFun` 落域：`G₁ ∪ G₂ ∪ {e} ⊆ E(S)` 且含 `e`
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, by simp⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact edgeWithin_mono sideOf_subset (Finset.mem_powerset.mp hp₁ hx)
      · exact edgeWithin_mono Finset.sdiff_subset (Finset.mem_powerset.mp hp₂ hx)
    · rw [Finset.mem_singleton] at hx
      rw [hx]; exact heS
  · -- (5) `left_inv`：`F ↦ (F₁,F₂) ↦ F₁ ∪ F₂ ∪ {e} = F`
    intro F hF
    obtain ⟨hFpow, heF⟩ := Finset.mem_filter.mp hF
    exact filter_pair_union_filter_eq_self (Finset.mem_powerset.mp hFpow) heF
  · -- (6) `right_inv`：`(G₁,G₂) ↦ G₁ ∪ G₂ ∪ {e} ↦ (G₁,G₂)`
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    exact Prod.ext (filter_pair_union_eq_self rfl (mem_sideOf_self haS) hbS₂
      (Finset.mem_powerset.mp hp₁) (Finset.mem_powerset.mp hp₂)).1
      (filter_pair_union_eq_self rfl (mem_sideOf_self haS) hbS₂
        (Finset.mem_powerset.mp hp₁) (Finset.mem_powerset.mp hp₂)).2
  · -- (7) 值一致：左端的 `F` 与右端 `invFun (toFun F)` 相同（由 `left_inv` 给出）
    intro F hF
    obtain ⟨hFpow, heF⟩ := Finset.mem_filter.mp hF
    rw [filter_pair_union_filter_eq_self (Finset.mem_powerset.mp hFpow) heF]

/-! ##### ★★ 和之劈分：**已知的最后一步**

`sum_filter_mem_bridge_eq_sum_pairs` 已把 `connSum I S` 重指标到对集合
`s₁.powerset ×ˢ s₂.powerset`（`s₁ := E(S₁)`、`s₂ := E(S∖S₁)`），
逐项恒等式 `ite_connected_mul_sign_eq_neg_mul` 已把每项换成 `−` 两半之积。

**剩下的两步**（纯代数，无新数学）：

1. 用 `Finset.sum_product` 把对集合上的和化成双重和
   `∑ G₁ ∈ s₁.powerset, ∑ G₂ ∈ s₂.powerset, …`；
2. 逐项用 `ite_connected_mul_sign_eq_neg_mul` 换成 `−(…)·(…)`，
   再 `rw [Finset.sum_mul_sum]`（或 `Finset.mul_sum` / `Finset.sum_mul`）
   提出常数并识别为 `− connSum I S₁ · connSum I S₂`。

**注意** `connSum` 定义里 `ite` 的分支与 `sum_pairs` 右侧的被加项形状需对齐
（`connSum` 用 `if … then … else 0`，而逐项恒等式用 `ite … … 0`，二者定义相同）。 -/

/-- **★★ 对集合上的和 = 双重和**（`Finset.sum_product` 的直接应用，供因子化步使用）。 -/
theorem sum_pairs_eq_sum_sum {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S S₁ : Finset V} {a b : V} (g : Finset (Sym2 V) → ℤ) :
    (∑ p ∈ (edgeWithin I S₁).powerset
            ×ˢ (edgeWithin I (S \ sideOf I S (s(a, b)) a)).powerset,
        g (p.1 ∪ p.2 ∪ {s(a, b)}))
      = ∑ G₁ ∈ (edgeWithin I S₁).powerset,
          ∑ G₂ ∈ (edgeWithin I (S \ sideOf I S (s(a, b)) a)).powerset,
            g (G₁ ∪ G₂ ∪ {s(a, b)}) :=
  Finset.sum_product _ _ _

set_option maxHeartbeats 4000000 in
/-- **★★★ 和之劈分（因子化）**：`e = s(a,b)` 是 `E(S)` 的割边、`a ∈ S` 时

> `connSum I S = − connSum I S₁ · connSum I S₂`（`S₁ := sideOf I S e a`）

**证法链**：`connSum_eq_sum_filter_mem_bridge`（限制到 `F ∋ e`）→
`sum_filter_mem_bridge_eq_sum_pairs`（`sum_bij'` 重指标到半对）→
`Finset.sum_product`（化双重和）→ 逐项恒等式 + 常数提取。 -/
theorem connSum_eq_neg_mul_connSum_connSum {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (heS : s(a, b) ∈ edgeWithin I S) (haS : a ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    connSum I S
      = - (connSum I (sideOf I S (s(a, b)) a)
            * connSum I (S \ sideOf I S (s(a, b)) a)) := by
  classical
  -- 第一步：限制到含 `e` 的子集，并重指标到半对
  rw [connSum_eq_sum_filter_mem_bridge heS hbridge,
    sum_filter_mem_bridge_eq_sum_pairs heS haS hbridge]
  -- 第二步：对集合上的和 = 双重和（只改左边；直接用 `sum_product`，避免 `?g` 统一失败）
  conv_lhs => rw [Finset.sum_product]
  -- 第三步：逐项换成分离形式
  have hterm : ∀ G₁ ∈ (edgeWithin I (sideOf I S (s(a, b)) a)).powerset,
      ∀ G₂ ∈ (edgeWithin I (S \ sideOf I S (s(a, b)) a)).powerset,
      (ite (((SimpleGraph.fromEdgeSet
            (↑(G₁ ∪ G₂ ∪ {s(a, b)}) : Set (Sym2 V))).induce (↑S : Set V)).Connected)
          ((-1 : ℤ) ^ (G₁ ∪ G₂ ∪ {s(a, b)}).card) 0)
        = -((ite (((SimpleGraph.fromEdgeSet (↑G₁ : Set (Sym2 V))).induce
                (↑(sideOf I S (s(a, b)) a) : Set V)).Connected)
              ((-1 : ℤ) ^ G₁.card) 0)
            * (ite (((SimpleGraph.fromEdgeSet (↑G₂ : Set (Sym2 V))).induce
                (↑(S \ sideOf I S (s(a, b)) a) : Set V)).Connected)
              ((-1 : ℤ) ^ G₂.card) 0)) := by
    intro G₁ hG₁ G₂ hG₂
    have hG₁' : G₁ ⊆ edgeWithin I (sideOf I S (s(a, b)) a) := Finset.mem_powerset.mp hG₁
    have hG₂' : G₂ ⊆ edgeWithin I (S \ sideOf I S (s(a, b)) a) := Finset.mem_powerset.mp hG₂
    -- `F := G₁ ∪ G₂ ∪ {e}` 落位
    have hFsub : G₁ ∪ G₂ ∪ {s(a, b)} ⊆ edgeWithin I S := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact edgeWithin_mono sideOf_subset (hG₁' hx)
        · exact edgeWithin_mono Finset.sdiff_subset (hG₂' hx)
      · rw [Finset.mem_singleton] at hx
        rw [hx]; exact heS
    have hFe : s(a, b) ∈ G₁ ∪ G₂ ∪ {s(a, b)} := by simp
    -- 逐项恒等式作用在 `F` 上
    have key := ite_connected_mul_sign_eq_neg_mul heS haS hbridge hFsub hFe
    -- 把 `F` 的两个 `filter` 半换成 `G₁`、`G₂`（右逆）
    have hpair := filter_pair_union_eq_self (I := I) (S := S)
      (S₁ := sideOf I S (s(a, b)) a) (G₁ := G₁) (G₂ := G₂) (a := a) (b := b)
      rfl (mem_sideOf_self haS)
      (Finset.mem_sdiff.mpr
        ⟨mem_of_mem_edgeWithin heS b (Sym2.mem_iff.mpr (Or.inr rfl)),
          not_mem_sideOf_b hbridge⟩) hG₁' hG₂'
    rw [hpair.1, hpair.2] at key
    exact key
  -- 第四步：把双重和的被加项逐点换成分离形式（内层再外层）
  rw [Finset.sum_congr rfl (fun G₁ hG₁ => Finset.sum_congr rfl (fun G₂ hG₂ =>
    hterm G₁ hG₁ G₂ hG₂))]
  -- 第五步：把 `-` 从两层和里提出
  simp_rw [Finset.sum_neg_distrib]
  rw [neg_inj]
  -- 内层：`∑ G₂, a · b G₂ = a · ∑ G₂, b G₂`（`a` 与 `G₂` 无关）
  rw [Finset.sum_congr rfl (fun G₁ _ => (Finset.mul_sum _ _ _).symm)]
  -- 外层：把与 `G₁` 无关的内层和提出来
  rw [← Finset.sum_mul]
  rw [connSum, connSum]

/-! ##### ★ 归纳步所需的**基数下降**事实

`e = s(a,b)` 是 `E(S)` 的割边、`a ∈ S`、`b ∈ S` 时，两侧都**真小**于 `S`：

* `|S₁| < |S|`：由 `b ∈ S`、`b ∉ S₁`（`not_mem_sideOf_b`）与 `S₁ ⊆ S`（`sideOf_subset`）；
* `|S ∖ S₁| < |S|`：由 `a ∈ S`、`a ∉ S ∖ S₁`（`a ∈ S₁`，`mem_sideOf_self`）与 `S∖S₁ ⊆ S`。 -/

omit [LinearOrder V] in
/-- **★ 一侧真小**：`e` 是割边、`b ∈ S` ⇒ `|sideOf I S e a| < |S|`。 -/
theorem card_sideOf_lt {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (hbS : b ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b)) :
    (sideOf I S (s(a, b)) a).card < S.card := by
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sideOf_subset, ?_⟩)
  intro h
  -- `h : sideOf … = S`；由 `h` 把目标里的 `sideOf …` 整体换成 `S`，再用 `hbS`
  exact not_mem_sideOf_b hbridge (by rw [h]; exact hbS)

/-- **★ 另一侧真小**：`e` 是割边、`a ∈ S` ⇒ `|S ∖ sideOf I S e a| < |S|`。 -/
theorem card_sdiff_sideOf_lt {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (haS : a ∈ S) :
    (S \ sideOf I S (s(a, b)) a).card < S.card := by
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩)
  intro h
  -- `h : S ∖ S₁ = S`；由 `h` 把目标里的 `S ∖ S₁` 整体换成 `S`，再用 `haS`
  exact (Finset.mem_sdiff.mp (by rw [h]; exact haS)).2 (mem_sideOf_self haS)

/-! ##### ★★★ 引理 3.1 的另一半：**归纳步**（目标 (2) 的可行部分）

**归纳陈述**（对 `S.card` 强归纳）：

> 若 `S` 在 `E(S)` 的诱导图上连通，则 `connSum I S ≠ 0`。

**归纳步（有割边时）**：若 `E(S)` 有割边 `e = s(a,b)`，则由第 37 段

> `connSum I S = − connSum I S₁ · connSum I S₂`

而 `|S₁| < |S|`、`|S ∖ S₁| < |S|`（`card_sideOf_lt` / `card_sdiff_sideOf_lt`），
两半各自连通（`connected_filter_sideOf_of_connected`），
故由归纳假设 `connSum I S₁ ≠ 0`、`connSum I S₂ ≠ 0`，乘积非零 ⇒ `connSum I S ≠ 0`。

**未完成的部分（目标 (3)）**：若 `E(S)` **无割边**（2-连通情形，如 `C₄`、`K₄`），
上述归纳步**不适用** —— 此时 `sideOf` 无意义，因子化无从谈起。
**本项目目前没有这条路线**：`connected S` 只保证连通，不保证有桥。

**故本段的归纳步只对"有桥的连通 `S`"成立**，无条件版本仍需 (3)。 -/

/-- **★ 归纳步（有割边时）**：`E(S)` 有割边 `e = s(a,b)`、两半都满足归纳假设
⇒ `connSum I S ≠ 0`。

这是目标 (2) 的**可行部分**；无桥情形（目标 (3)）不在本引理覆盖内。 -/
theorem connSum_ne_zero_of_isBridge {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} {a b : V} (heS : s(a, b) ∈ edgeWithin I S) (haS : a ∈ S)
    (hbridge : (edgeGraph I S).IsBridge s(a, b))
    (h₁ : connSum I (sideOf I S (s(a, b)) a) ≠ 0)
    (h₂ : connSum I (S \ sideOf I S (s(a, b)) a) ≠ 0) :
    connSum I S ≠ 0 := by
  rw [connSum_eq_neg_mul_connSum_connSum heS haS hbridge]
  exact neg_ne_zero.mpr (mul_ne_zero h₁ h₂)

end Pphi2Ursell
