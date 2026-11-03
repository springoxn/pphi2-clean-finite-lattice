/-
Ursell/Mayer 组合核的**第六块** —— 定理 3.2（连通图公式）的**基础层**：
把"连通生成子图的 `(−1)^{|E|}` 求和"定义出来（`connSum`），并验证它在**无边**情形下与 `φ` 一致。

**口径**：`proofs/pphi2_cluster_expansion.md` 定理 3.2：
`𝕀(X)` 连通时 `φ(X) = Σ_{G ⊆ 𝕀(X), G 连通生成} (−1)^{|E(G)|}`。
本文件只做**定义**与"`𝕀(S)` 无边 ⇒ `connSum = 0`"这一半（与 `ursell_eq_zero_of_compatible` 对齐）。

**本文件证了什么**
1. `edgeWithin`：`S` 内部的边（`I.edgeFinset` 里两个端点都在 `S` 的边）。
2. `connSum`：`Σ_{F ⊆ 边(S)} (−1)^{|F|} · [((S, F) 生成) 连通]`（定理 3.2 的右端）。
3. `edgeWithin_eq_empty`：`S` 相容（无边）⇒ 内部无任何边。
4. `connSum_eq_zero_of_isCompatible`：`S` 相容且 `|S| ≥ 2` ⇒ `connSum = 0`（与 `φ` 对齐）。

**明确不在本文件内**：`connSum` 的续接方程（= 定理 3.2 的证明本体）、
引理 3.1 的另一半（连通 ⇒ `φ ≠ 0`）、定理 3.3、`(2.1)`。
-/
import S6Isserlis.UrsellGeneral
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

noncomputable section

open scoped Classical
open Finset

namespace Pphi2Ursell

variable {V : Type*} [LinearOrder V]

/-! ### §9 定理 3.2 的基础层：连通生成子图的交错和 -/

/-- `S` **内部**的边：`I` 的边表中两个端点都落在 `S` 里的那些。 -/
def edgeWithin (I : SimpleGraph V) [Fintype ↑I.edgeSet] (S : Finset V) : Finset (Sym2 V) :=
  I.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)

/-- **定理 3.2 的右端**：`S` 上"连通生成子图"的 `(−1)^{|E|}` 求和
（`F` 遍历 `S` 内部边的所有子集；生成性由 `induce S` 自动带上）。 -/
def connSum (I : SimpleGraph V) [Fintype ↑I.edgeSet] (S : Finset V) : ℤ :=
  ∑ F ∈ (edgeWithin I S).powerset,
    if ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).induce (↑S : Set V)).Connected then
      (-1 : ℤ) ^ F.card
    else 0

omit [LinearOrder V] in
/-- `S` 相容（无边）⇒ `S` 内部没有任何边。 -/
theorem edgeWithin_eq_empty {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    (h : IsCompatible I S) : edgeWithin I S = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨e, he⟩
  revert he
  refine Sym2.ind (fun v w => ?_) e
  intro he
  rw [edgeWithin, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
  obtain ⟨hvw, hsub⟩ := he
  rw [SimpleGraph.mem_edgeSet] at hvw
  have hv : v ∈ S := hsub v (Sym2.mem_iff.mpr (Or.inl rfl))
  have hw : w ∈ S := hsub w (Sym2.mem_iff.mpr (Or.inr rfl))
  have hne : v ≠ w := fun hvw' => SimpleGraph.irrefl I (hvw' ▸ hvw)
  exact h v hv w hw hne hvw

/-- 空边集的图就是无边图。 -/
private theorem fromEdgeSet_empty {V : Type*} :
    SimpleGraph.fromEdgeSet (↑(∅ : Finset (Sym2 V)) : Set (Sym2 V)) = ⊥ := by
  ext v w
  rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.bot_adj]
  simp

/-- **无边情形与 `φ` 对齐**：`S` 相容且 `|S| ≥ 2` ⇒ `connSum I S = 0`
（对应 `ursell_eq_zero_of_compatible`）。 -/
theorem connSum_eq_zero_of_isCompatible {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V}
    (hcomp : IsCompatible I S) (hcard : 2 ≤ S.card) : connSum I S = 0 := by
  have hnot : ¬ Subsingleton (↥S) := fun hsub => by
    have h1 : S.card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => Subtype.ext_iff.mp (hsub.elim ⟨a, ha⟩ ⟨b, hb⟩)
    omega
  have hcond : ¬ ((SimpleGraph.fromEdgeSet (↑(∅ : Finset (Sym2 V)) : Set (Sym2 V))).induce
      (↑S : Set V)).Connected := by
    rw [fromEdgeSet_empty, SimpleGraph.induce_bot, SimpleGraph.connected_bot_iff]
    exact fun h => hnot h.1
  rw [connSum, edgeWithin_eq_empty hcomp, Finset.powerset_empty, Finset.sum_singleton]
  exact ite_eq_right hcond

omit [LinearOrder V] in
/-- `S` 内部无边 ⟺ `S` 相容。 -/
theorem edgeWithin_eq_empty_iff {I : SimpleGraph V} [Fintype ↑I.edgeSet] {S : Finset V} :
    edgeWithin I S = ∅ ↔ IsCompatible I S := by
  refine ⟨fun h u hu v hv huv hadj => ?_, edgeWithin_eq_empty⟩
  have hmem : s(u, v) ∈ edgeWithin I S := by
    rw [edgeWithin, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hadj, fun x hx => by
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hu
      · exact hv⟩
  rw [h] at hmem
  exact Finset.notMem_empty _ hmem

omit [LinearOrder V] in
/-- `∑_{F ⊆ E} (−1)^{|F|} = [E = ∅]`（`E` 为空给 `1`，否则给 `0`）。 -/
private theorem sum_powerset_neg_one_pow_card {α : Type*} :
    ∀ E : Finset α, ∑ F ∈ E.powerset, (-1 : ℤ) ^ F.card = if E = ∅ then 1 else 0 := by
  intro E
  induction E using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [ite_eq_right (fun h => Finset.notMem_empty a (by rw [← h]; exact Finset.mem_insert_self a s)),
      Finset.powerset_insert]
    have hdisj : Disjoint s.powerset (s.powerset.image (fun t => insert a t)) := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      obtain ⟨t₀, ht₀, hEq⟩ := Finset.mem_image.mp ht'
      rw [← hEq] at ht
      exact ha (Finset.mem_powerset.mp ht (Finset.mem_insert_self a t₀))
    have hinj : Set.InjOn (fun t : Finset α => insert a t) ↑s.powerset := by
      intro t ht t' ht' hEq
      have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
      have hat' : a ∉ t' := fun h => ha (Finset.mem_powerset.mp ht' h)
      have h' := congrArg (fun u : Finset α => u.erase a) hEq
      simpa [Finset.erase_insert hat, Finset.erase_insert hat'] using h'
    rw [Finset.sum_union hdisj, Finset.sum_image hinj, ih]
    have h2 : ∀ t ∈ s.powerset, (-1 : ℤ) ^ (insert a t).card = (-1 : ℤ) ^ t.card * (-1) := by
      intro t ht
      have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
      rw [Finset.card_insert_of_notMem hat, pow_succ]
    rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, ih]
    by_cases hs : s = ∅ <;> simp [hs]

omit [LinearOrder V] in
/-- **3.2 的左侧**：`S` 内部边的**所有**子集上的交错和 = `[S 相容]`（即 `compatInd I S`）。
这是定理 3.2 证明里"按 `min S` 所在连通分量分解"之前的整体恒等式。 -/
theorem sum_neg_one_pow_card_edgeWithin {I : SimpleGraph V} [Fintype ↑I.edgeSet] (S : Finset V) :
    (∑ F ∈ (edgeWithin I S).powerset, (-1 : ℤ) ^ F.card) = compatInd I S := by
  rw [sum_powerset_neg_one_pow_card, compatInd]
  by_cases h : IsCompatible I S
  · rw [ite_eq_left h, ite_eq_left (edgeWithin_eq_empty_iff.mpr h)]
  · rw [ite_eq_right h]
    exact ite_eq_right fun hemp => h (edgeWithin_eq_empty_iff.mp hemp)

/-- **3.2 的最小实例（单点）**：`connSum I {i} = 1`，与 `ursell_singleton` 一致
（`{i}` 内部无任何边 ⇒ 只有 `F = ∅` 一项，而单点图的 `induce` 连通）。 -/
theorem connSum_singleton {I : SimpleGraph V} [Fintype ↑I.edgeSet] (i : V) :
    connSum I {i} = 1 := by
  have hsub : Subsingleton (↥({i} : Finset V)) :=
    ⟨fun a b => Subtype.ext (by
      have ha : a.1 = i := Finset.mem_singleton.mp a.2
      have hb : b.1 = i := Finset.mem_singleton.mp b.2
      rw [ha, hb])⟩
  have hne : Nonempty (↥({i} : Finset V)) := ⟨⟨i, Finset.mem_singleton_self i⟩⟩
  have hcond : ((SimpleGraph.fromEdgeSet (↑(∅ : Finset (Sym2 V)) : Set (Sym2 V))).induce
      (↑({i} : Finset V) : Set V)).Connected := by
    rw [fromEdgeSet_empty, SimpleGraph.induce_bot, SimpleGraph.connected_bot_iff]
    exact ⟨hsub, hne⟩
  rw [connSum, edgeWithin_eq_empty (isCompatible_singleton I i), Finset.powerset_empty,
    Finset.sum_singleton, ite_eq_left hcond]
  simp

/-! ### §10 3.2 双射的边集簿记（蓝图 §4.13.1 的装配件） -/

omit [LinearOrder V] in
/-- `edgeWithin` 对集合单调。 -/
theorem edgeWithin_mono {I : SimpleGraph V} [Fintype ↑I.edgeSet] {A B : Finset V} (h : A ⊆ B) :
    edgeWithin I A ⊆ edgeWithin I B := by
  intro e he
  rw [edgeWithin, Finset.mem_filter] at he ⊢
  exact ⟨he.1, fun v hv => h (he.2 v hv)⟩

omit [LinearOrder V] in
/-- 不相交的两个顶点集上的内部边集**不相交**（一条边的两个端点不可能一在 `A` 一在 `B` 又同时在两边）。 -/
theorem edgeWithin_disjoint {I : SimpleGraph V} [Fintype ↑I.edgeSet] {A B : Finset V}
    (h : Disjoint A B) : Disjoint (edgeWithin I A) (edgeWithin I B) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  revert heA heB
  refine Sym2.ind (fun v w => ?_) e
  intro heA heB
  rw [edgeWithin, Finset.mem_filter] at heA heB
  exact Finset.disjoint_left.mp h (heA.2 v (Sym2.mem_iff.mpr (Or.inl rfl)))
    (heB.2 v (Sym2.mem_iff.mpr (Or.inl rfl)))

/-- `edgeWithin I A ∪ edgeWithin I B ⊆ edgeWithin I (A ∪ B)`。 -/
theorem edgeWithin_union_subset {I : SimpleGraph V} [Fintype ↑I.edgeSet] (A B : Finset V) :
    edgeWithin I A ∪ edgeWithin I B ⊆ edgeWithin I (A ∪ B) := by
  intro e he
  rw [Finset.mem_union] at he
  rcases he with he | he
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp
      (show e ∈ I.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ A) from he)
    exact Finset.mem_filter.mpr ⟨h1, fun v hv => Finset.mem_union_left B (h2 v hv)⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp
      (show e ∈ I.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ B) from he)
    exact Finset.mem_filter.mpr ⟨h1, fun v hv => Finset.mem_union_right A (h2 v hv)⟩

/-- 不相交顶点集上内部边集的基数可加（双射单射性要用的"边不重"）。 -/
theorem card_edgeWithin_union {I : SimpleGraph V} [Fintype ↑I.edgeSet] {A B : Finset V}
    (h : Disjoint A B) :
    (edgeWithin I A ∪ edgeWithin I B).card = (edgeWithin I A).card + (edgeWithin I B).card :=
  Finset.card_union_of_disjoint (edgeWithin_disjoint h)

omit [LinearOrder V] in
/-- **指数因子**：`(−1)^{|F_A ⊎ F_B|} = (−1)^{|F_A|}·(−1)^{|F_B|}`（蓝图 §4.13.1 第 3 步）。 -/
theorem neg_one_pow_card_union {α : Type*} {A B : Finset α} (h : Disjoint A B) :
    (-1 : ℤ) ^ (A ∪ B).card = (-1 : ℤ) ^ A.card * (-1 : ℤ) ^ B.card := by
  rw [Finset.card_union_of_disjoint h, pow_add]

/-! ### §11 3.2 续接方程的**相容情形** -/

/-- **`connSum` 的续接方程（`S` 相容时）**：右端只剩 `A = {min S}` 一项
（其余 `A` 因 `|A| ≥ 2` 而 `connSum = 0`），故 RHS `= 1 = [S 相容]`。 -/
theorem compatInd_eq_sum_connSum_of_isCompatible {I : SimpleGraph V} [Fintype ↑I.edgeSet]
    {S : Finset V} (hS : S.Nonempty) (hcomp : IsCompatible I S) :
    compatInd I S = ∑ A ∈ S.powerset.filter (fun A => S.min' hS ∈ A),
      connSum I A * compatInd I (S \ A) := by
  have hcomp_sub : ∀ {A : Finset V}, A ⊆ S → IsCompatible I A := fun hsub u hu v hv huv hadj =>
    hcomp u (hsub hu) v (hsub hv) huv hadj
  have hcomp_diff : ∀ A : Finset V, IsCompatible I (S \ A) := fun A u hu v hv huv hadj =>
    hcomp u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1 huv hadj
  rw [compatInd, ite_eq_left hcomp,
    Finset.sum_eq_single ({S.min' hS} : Finset V)]
  · rw [connSum_singleton, compatInd, ite_eq_left (hcomp_diff {S.min' hS}), one_mul]
  · intro A hA hne
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    obtain ⟨hsub, hmA⟩ := hA
    have hcard : 2 ≤ A.card := by
      rcases Nat.lt_or_ge A.card 2 with h | h
      · have hpos : 0 < A.card := Finset.card_pos.mpr ⟨S.min' hS, hmA⟩
        have h1 : A.card = 1 := by omega
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
        rw [Finset.mem_singleton] at hmA
        exact absurd (by rw [hmA]) hne
      · exact h
    rw [connSum_eq_zero_of_isCompatible (hcomp_sub hsub) hcard, zero_mul]
  · intro h
    exact absurd (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr (Finset.min'_mem S hS)),
        Finset.mem_singleton_self (S.min' hS)⟩) h

/-! ### §12 互不相邻的两个集合上边集的加性 -/

/-- 若 `A`、`B` 不交且之间没有 `I`-边，则 `A ∪ B` 的内部边集是两个内部边集之并。 -/
theorem edgeWithin_union_eq {I : SimpleGraph V} [Fintype ↑I.edgeSet] {A B : Finset V}
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ I.Adj a b) :
    edgeWithin I (A ∪ B) = edgeWithin I A ∪ edgeWithin I B := by
  refine Finset.Subset.antisymm ?_ (edgeWithin_union_subset A B)
  intro e he
  rw [Finset.mem_union]
  revert he
  refine Sym2.ind (fun v w => ?_) e
  intro he
  obtain ⟨hvw, hsub⟩ := Finset.mem_filter.mp
    (show s(v, w) ∈ I.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ A ∪ B) from he)
  have hvw' : I.Adj v w := by
    rw [← SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.mem_edgeFinset.mp hvw)
  have hv : v ∈ A ∨ v ∈ B := Finset.mem_union.mp (hsub v (Sym2.mem_iff.mpr (Or.inl rfl)))
  have hw : w ∈ A ∨ w ∈ B := Finset.mem_union.mp (hsub w (Sym2.mem_iff.mpr (Or.inr rfl)))
  have key : ∀ {C : Finset V}, v ∈ C → w ∈ C → I.Adj v w → s(v, w) ∈ edgeWithin I C :=
    fun hvC hwC hadj => Finset.mem_filter.mpr ⟨by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj, fun x hx => by
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hvC
        · exact hwC⟩
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact Or.inl (key hv hw hvw')
  · exact absurd hvw' (hcross v hv w hw)
  · exact absurd ((SimpleGraph.adj_comm I v w).mp hvw') (hcross w hw v hv)
  · exact Or.inr (key hv hw hvw')

/-- `connSum I ∅ = 0`（与 `ursell_empty` 一致：空集没有顶点，`induce ∅` 不是连通图）。 -/
theorem connSum_empty {I : SimpleGraph V} [Fintype ↑I.edgeSet] : connSum I (∅ : Finset V) = 0 := by
  rw [connSum]
  refine Finset.sum_eq_zero (fun F _ => ?_)
  refine ite_eq_right ?_
  rw [SimpleGraph.connected_iff]
  rintro ⟨-, ⟨x, hx⟩⟩
  simp at hx

end Pphi2Ursell
