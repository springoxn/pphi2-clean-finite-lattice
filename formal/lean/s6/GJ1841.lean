import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card.Arithmetic

/-!
# GJ 2nd ed (18.4.1) 的 **L1（森林界）** —— M2 组合层第一块

来源：`proofs/pphi2_gj_1841_general.md` §1.2（本项目 ROUND 32 给出的一般证明）；
书：Glimm–Jaffe, *Quantum Physics*, 2nd ed, 印刷 p.368（PDF 384）。

本文件机械化 **L1**：
* `card_vert_sub_card_connectedComponent_le_card_edgeSet`：任意有限图 `#V - #分量 ≤ #E`；
* `IsAcyclic.card_vert_le_card_edgeSet_add_card_connectedComponent`：无圈情形**取等**。

**范围内**：只到 L1。**范围外**（见 `formal/lean/M2_keystone18_plan.md`）：
L2（角引理）、L3（分量数上界）、装配 T，以及单位方块模型
（`X` = 闭单位方格之并、格线 `Γ`、`Int X`、方格图 `H`）。

**诚实边界**：这是**纯图论**事实，与 P(φ)₂ 的具体几何无关；它是 `(18.4.1)` 装配的第一块，
**不**表示 `PPHI2_ACTIVITY_BOUND`（核 B）已闭合 —— `(18.7.A)` 的合并记账仍 OPEN。

**取径说明（与 `M2_keystone18_plan.md` §5 的差异）**：边和**没有**走
`card_filter_edgeFinset_toFinset_subset` + `Finset.card_eq_sum_card_fiberwise` 的 `edgeFinset`
纤维路线，而是走**集合层的spanning-graph 划分**（`iUnion_spanningCoe_edgeSet` +
`pairwise_disjoint_spanningCoe_edgeSet` + `ncard_edgeSet_spanningCoe`），更短且不碰 `edgeFinset`。
-/

noncomputable section
open scoped Classical

open scoped BigOperators
open SimpleGraph

namespace GJ1841

-- D1: vertex sum
/-- The vertices of `G` are the disjoint union of the supports of its connected components. -/
lemma sum_ncard_supp_connectedComponent {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∑ C : G.ConnectedComponent, C.supp.ncard = Nat.card V := by
  classical
  have hcard : (⋃ C : G.ConnectedComponent, C.supp).ncard =
      ∑ᶠ C : G.ConnectedComponent, C.supp.ncard :=
    Set.ncard_iUnion_of_finite (s := fun C : G.ConnectedComponent => C.supp)
      (hs := fun _ => Set.toFinite _)
      (h := SimpleGraph.pairwise_disjoint_supp_connectedComponent G)
  calc
    ∑ C : G.ConnectedComponent, C.supp.ncard
        = ∑ᶠ C : G.ConnectedComponent, C.supp.ncard :=
          (finsum_eq_sum_of_fintype (fun C : G.ConnectedComponent => C.supp.ncard)).symm
    _ = (⋃ C : G.ConnectedComponent, C.supp).ncard := hcard.symm
    _ = (Set.univ : Set V).ncard := by
          rw [SimpleGraph.iUnion_connectedComponentSupp G]
    _ = Nat.card V := Set.ncard_univ V

/-! ### D2: edge sum -/

/-- Characterisation of the edges of the spanning graph of a connected component. -/
lemma mem_spanningCoe_edgeSet_mk_iff {V : Type*} (G : SimpleGraph V) {C : G.ConnectedComponent}
    {x y : V} :
    s(x, y) ∈ (C.toSimpleGraph.spanningCoe).edgeSet ↔ x ∈ C.supp ∧ y ∈ C.supp ∧ G.Adj x y := by
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph]
  constructor
  · rintro ⟨hx, hadj⟩
    exact ⟨hx, (SimpleGraph.ConnectedComponent.mem_supp_congr_adj C hadj).mp hx, hadj⟩
  · rintro ⟨hx, _hy, hadj⟩
    exact ⟨hx, hadj⟩

/-- The edges of `G` are the disjoint union of the edges of the spanning graphs of its
connected components. -/
lemma iUnion_spanningCoe_edgeSet {V : Type*} (G : SimpleGraph V) :
    (⋃ C : G.ConnectedComponent, (C.toSimpleGraph.spanningCoe).edgeSet) = G.edgeSet := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph,
      Set.mem_iUnion]
    constructor
    · rintro ⟨C, hx, hadj⟩
      exact hadj
    · intro hadj
      refine ⟨G.connectedComponentMk x, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, hadj⟩

/-- The spanning graphs of distinct connected components have disjoint edge sets. -/
lemma pairwise_disjoint_spanningCoe_edgeSet {V : Type*} (G : SimpleGraph V) :
    Pairwise fun (C C' : G.ConnectedComponent) =>
      Disjoint (C.toSimpleGraph.spanningCoe).edgeSet (C'.toSimpleGraph.spanningCoe).edgeSet := by
  intro C C' hne
  rw [Set.disjoint_left]
  intro e heC heC'
  induction e using Sym2.inductionOn with
  | _ x y =>
    rw [mem_spanningCoe_edgeSet_mk_iff] at heC heC'
    exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex heC.1 heC'.1)

/-- The edge set of `C.toSimpleGraph` and of its spanning graph have the same cardinality. -/
lemma ncard_edgeSet_spanningCoe {V : Type*} (G : SimpleGraph V) (C : G.ConnectedComponent) :
    ((C.toSimpleGraph).edgeSet).ncard = ((C.toSimpleGraph.spanningCoe).edgeSet).ncard := by
  rw [SimpleGraph.edgeSet_map]
  exact (Set.ncard_image_of_injective _
    ((Function.Embedding.subtype (p := fun v : V => v ∈ C.supp)).sym2Map.inj')).symm

-- D2: edge sum
/-- The edges of `G` are counted by summing the edges of each connected component's induced graph. -/
lemma sum_natCard_edgeSet_connectedComponent {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∑ C : G.ConnectedComponent, Nat.card (C.toSimpleGraph).edgeSet = Nat.card G.edgeSet := by
  classical
  have hcard : (⋃ C : G.ConnectedComponent, (C.toSimpleGraph.spanningCoe).edgeSet).ncard =
      ∑ᶠ C : G.ConnectedComponent, ((C.toSimpleGraph.spanningCoe).edgeSet).ncard :=
    Set.ncard_iUnion_of_finite
      (s := fun C : G.ConnectedComponent => (C.toSimpleGraph.spanningCoe).edgeSet)
      (hs := fun _ => Set.toFinite _)
      (h := pairwise_disjoint_spanningCoe_edgeSet G)
  calc
    ∑ C : G.ConnectedComponent, Nat.card (C.toSimpleGraph).edgeSet
        = ∑ C : G.ConnectedComponent, ((C.toSimpleGraph).edgeSet).ncard := by
            refine Finset.sum_congr rfl fun C _ => Nat.card_coe_set_eq ((C.toSimpleGraph).edgeSet)
    _ = ∑ C : G.ConnectedComponent, ((C.toSimpleGraph.spanningCoe).edgeSet).ncard := by
            refine Finset.sum_congr rfl fun C _ => ncard_edgeSet_spanningCoe G C
    _ = ∑ᶠ C : G.ConnectedComponent, ((C.toSimpleGraph.spanningCoe).edgeSet).ncard :=
            (finsum_eq_sum_of_fintype
              (fun C : G.ConnectedComponent => ((C.toSimpleGraph.spanningCoe).edgeSet).ncard)).symm
    _ = (⋃ C : G.ConnectedComponent, (C.toSimpleGraph.spanningCoe).edgeSet).ncard := hcard.symm
    _ = G.edgeSet.ncard := by rw [iUnion_spanningCoe_edgeSet G]
    _ = Nat.card G.edgeSet := (Nat.card_coe_set_eq G.edgeSet).symm

/-! ### D3: main theorem (forest bound, Glimm–Jaffe (18.4.1) L1) -/

/-- The per-component bound: a connected graph on `C.supp` has at least `ncard C.supp - 1` edges. -/
lemma ncard_supp_le_edgeSet_add_one {V : Type*} (G : SimpleGraph V) (C : G.ConnectedComponent) :
    C.supp.ncard ≤ Nat.card (C.toSimpleGraph).edgeSet + 1 := by
  calc
    C.supp.ncard = Nat.card C := (Nat.card_coe_set_eq C.supp).symm
    _ ≤ Nat.card (C.toSimpleGraph).edgeSet + 1 :=
          C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one

/-- Glimm–Jaffe (18.4.1) "forest bound" L1: for a finite graph, the number of vertices minus the
number of connected components is at most the number of edges. -/
theorem card_vert_sub_card_connectedComponent_le_card_edgeSet
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Nat.card V - Fintype.card G.ConnectedComponent ≤ Nat.card G.edgeSet := by
  classical
  have hsum : ∑ C : G.ConnectedComponent, C.supp.ncard ≤
      ∑ C : G.ConnectedComponent, (Nat.card (C.toSimpleGraph).edgeSet + 1) := by
    refine Finset.sum_le_sum fun C _ => ncard_supp_le_edgeSet_add_one G C
  have h : Nat.card V ≤ Nat.card G.edgeSet + Fintype.card G.ConnectedComponent := by
    calc
      Nat.card V = ∑ C : G.ConnectedComponent, C.supp.ncard :=
            (sum_ncard_supp_connectedComponent G).symm
      _ ≤ ∑ C : G.ConnectedComponent, (Nat.card (C.toSimpleGraph).edgeSet + 1) := hsum
      _ = (∑ C : G.ConnectedComponent, Nat.card (C.toSimpleGraph).edgeSet) +
            ∑ C : G.ConnectedComponent, 1 := by
            rw [Finset.sum_add_distrib]
      _ = Nat.card G.edgeSet + Fintype.card G.ConnectedComponent := by
            rw [sum_natCard_edgeSet_connectedComponent G]
            simp
  exact (Nat.sub_le_iff_le_add).2 h

/-! ### Stretch goal: forest formula (acyclic case) -/

/-- For an acyclic graph, each component is a tree, so its support has exactly
`edgeSet + 1` vertices. -/
lemma ncard_supp_eq_edgeSet_add_one_of_isAcyclic {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : G.IsAcyclic) (C : G.ConnectedComponent) :
    C.supp.ncard = Nat.card (C.toSimpleGraph).edgeSet + 1 := by
  have htree : C.toSimpleGraph.IsTree := h.isTree_connectedComponent C
  have hcard : Nat.card (C.toSimpleGraph).edgeSet + 1 = C.supp.ncard := by
    have h1 : Nat.card (C.toSimpleGraph).edgeSet + 1 = Nat.card C :=
      ((SimpleGraph.isTree_iff_connected_and_card (G := C.toSimpleGraph)).mp htree).2
    rwa [show Nat.card C = C.supp.ncard from Nat.card_coe_set_eq C.supp] at h1
  exact hcard.symm

/-- Glimm–Jaffe forest formula: for an acyclic finite graph, the number of vertices is at most
the number of edges plus the number of connected components (in fact equality holds). -/
theorem IsAcyclic.card_vert_le_card_edgeSet_add_card_connectedComponent
    {V : Type*} [Fintype V] (G : SimpleGraph V) (h : G.IsAcyclic) :
    Nat.card V ≤ Nat.card G.edgeSet + Fintype.card G.ConnectedComponent := by
  classical
  have heq : Nat.card V = Nat.card G.edgeSet + Fintype.card G.ConnectedComponent := by
    calc
      Nat.card V = ∑ C : G.ConnectedComponent, C.supp.ncard :=
            (sum_ncard_supp_connectedComponent G).symm
      _ = ∑ C : G.ConnectedComponent, (Nat.card (C.toSimpleGraph).edgeSet + 1) := by
            refine Finset.sum_congr rfl fun C _ => ncard_supp_eq_edgeSet_add_one_of_isAcyclic G h C
      _ = Nat.card G.edgeSet + Fintype.card G.ConnectedComponent := by
            rw [Finset.sum_add_distrib, sum_natCard_edgeSet_connectedComponent G]
            simp
  exact le_of_eq heq


end GJ1841
