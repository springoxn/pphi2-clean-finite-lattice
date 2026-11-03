/-
Ursell/Mayer 组合核的**递推骨架** —— 节点 `PPHI2_CE_URSELL`（P(φ)₂ 团簇展开的组合核）的
第一块 Lean 形式化：项目口径 `proofs/pphi2_cluster_expansion.md` 的 `(2.2)` 递推，
以及引理 3.1（连通性引理）中**"不可相容图无边 ⇒ `φ = 0`"那一半**。

**口径（逐条对照 `proofs/pphi2_cluster_expansion.md`）**

* 聚合物集合 = 有限集 `S : Finset V`（`V` 带线性序，供 `min'` 取"块内最小元"）；
* 不可相容图 `I : SimpleGraph V`（`I.Adj i j` ⟺ `i ι j`）。书里写 `𝕀` **含自环**；
  这里取 Lean 的 `SimpleGraph` 口径（**无自环**），而"相容集"只排除**不同**元素之间的
  不相容 —— 与探针 CE0–CE4 的读数一致（单元素集恒相容）。
* **相容集** `IsCompatible I S` := `S` 中任何**两个不同**元素都不可不相容（= `I` 的独立集）。
* **Ursell 函数** `ursell I S` = `(2.2)` 的递推解（对 `S.card` 良基递归）：
  `φ(S) = [S 相容] − Σ_{A ∋ min S, A ⊊ S} φ(A)·[S∖A 相容]`，
  约定 `φ(∅) = 0`。

**本文件证了什么**（每条都是上面口径下的定理，不是定义的重述）：

1. `ursell_empty` / `ursell_singleton`：`φ(∅) = 0`、`φ({i}) = 1`；
2. `ursell_pair_eq_neg_one`：`i ≠ j` 且 `i ι j` ⇒ `φ({i,j}) = −1`（对应 CE0 的 `n = 2` 读数）；
3. `compatInd_eq_sum`：`(2.2)` 的**更新方程**（= CE0 交叉验证用的那条）
   `[S 相容] = Σ_{A ∋ min S, A ⊆ S} φ(A)·[S∖A 相容]`（含 `A = S` 项）；
4. `ursell_eq_zero_of_compatible`：**引理 3.1 的一个真情形** —— `S` 完全相容
   （等价于 `𝕀(S)` **无边**；`|S| ≥ 2` 时当然不连通）⇒ `φ(S) = 0`。

**明确不在本文件内**（诚实边界）：

* `(2.1)` 指数公式的**形式幂级数**路线（`φ(X) = [∏ w_i] log Ξ`）；
* 引理 3.1 的**另一半**（`𝕀(X)` 连通 ⇒ `φ(X) ≠ 0`）；
* 引理 3.1 的一般形式（`𝕀(S)` 不连通但**有边** ⇒ `φ(S) = 0`）—— 本文件只证"无边"情形；
* 定理 3.2（连通图公式）与定理 3.3（树图界）；
* 任何解析内容（聚合物活度、测度）—— 本文件只有组合核。
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

noncomputable section

open scoped Classical
open Finset

namespace Pphi2Ursell

/-! ### §1 相容集与指示子 -/

/-- `S` 是**相容集**：`S` 中任何两个**不同**元素都不可不相容（= 不可相容图 `I` 的独立集）。

书的 `𝕀` 含自环；这里用无自环的 `SimpleGraph` 口径 ⇒ 单元素集恒相容（与 CE0–CE4 一致）。 -/
def IsCompatible {V : Type*} (I : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ I.Adj u v

/-- 相容性的 ℤ 值指示子（便于做 `(2.2)` 的加减法）。 -/
def compatInd {V : Type*} (I : SimpleGraph V) (S : Finset V) : ℤ :=
  if IsCompatible I S then 1 else 0

theorem isCompatible_empty {V : Type*} (I : SimpleGraph V) : IsCompatible I ∅ := by
  intro u hu
  simp at hu

theorem isCompatible_singleton {V : Type*} (I : SimpleGraph V) (i : V) : IsCompatible I {i} := by
  intro u hu v hv huv
  rw [Finset.mem_singleton] at hu hv
  exact absurd (hu.trans hv.symm) huv

protected theorem IsCompatible.mono {V : Type*} {I : SimpleGraph V} {S T : Finset V}
    (h : IsCompatible I S) (hTS : T ⊆ S) : IsCompatible I T :=
  fun u hu v hv huv => h u (hTS hu) v (hTS hv) huv

@[simp] theorem compatInd_empty {V : Type*} (I : SimpleGraph V) : compatInd I ∅ = 1 := by
  simp [compatInd, isCompatible_empty]

/-- **相容性在"横向相容的不交并"下可乘** —— 引理 3.1 的证明只用这一条结构性质。 -/
theorem isCompatible_union_iff {V : Type*} {I : SimpleGraph V} {A B : Finset V}
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ I.Adj a b) :
    IsCompatible I (A ∪ B) ↔ IsCompatible I A ∧ IsCompatible I B := by
  constructor
  · intro h
    exact ⟨h.mono Finset.subset_union_left, h.mono Finset.subset_union_right⟩
  · rintro ⟨hA, hB⟩ u hu v hv huv
    rw [Finset.mem_union] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hA u hu v hv huv
    · exact hcross u hu v hv
    · exact fun h => hcross v hv u hu ((SimpleGraph.adj_comm I v u).mpr h)
    · exact hB u hu v hv huv

/-! ### §2 Ursell 函数：`(2.2)` 的递推 -/

/-- 良基递归的递减证据（第一形式）。 -/
private theorem card_lt_of_subset_ne {V : Type*} {S T : Finset V} (hsub : T ⊆ S) (hne : T ≠ S) :
    T.card < S.card :=
  Finset.card_lt_card (lt_of_le_of_ne hsub hne)

/-- 良基递归的递减证据：`(2.2)` 里那个 filter 的成员都是 `S` 的**真**子集。 -/
private theorem card_lt_of_mem_filter {V : Type*} {S T : Finset V}
    (hsub : T ∈ S.powerset) (hne : T ≠ S) : T.card < S.card :=
  card_lt_of_subset_ne (Finset.mem_powerset.mp hsub) hne

set_option maxHeartbeats 2000000 in
/-- **Ursell/Mayer 函数**：项目口径 `(2.2)` 的递推解（对 `S.card` 良基递归）。

`φ(S) = [S 相容] − Σ_{A ∋ min S, A ⊊ S} φ(A)·[S∖A 相容]`，`φ(∅) = 0`。 -/
def ursell {V : Type*} [LinearOrder V] (I : SimpleGraph V) (S : Finset V) : ℤ :=
  (InvImage.wf Finset.card Nat.lt_wfRel.wf).fix
    (fun S rec =>
      if h : S.Nonempty then
        compatInd I S -
          ∑ A ∈ S.powerset.filter (fun T => S.min' h ∈ T ∧ T ≠ S),
            (if hc : A.card < S.card then rec A hc * compatInd I (S \ A) else 0)
      else 0) S

/-- `(2.2)` 的展开形式（`S` 非空）。 -/
theorem ursell_eq_of_nonempty {V : Type*} [LinearOrder V] (I : SimpleGraph V) {S : Finset V}
    (hS : S.Nonempty) :
    ursell I S =
      compatInd I S -
        ∑ A ∈ S.powerset.filter (fun T => S.min' hS ∈ T ∧ T ≠ S),
          ursell I A * compatInd I (S \ A) := by
  rw [ursell, WellFounded.fix_eq, dite_eq_left hS]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro A hA
  rw [dite_eq_left (card_lt_of_mem_filter (Finset.mem_filter.mp hA).1
    (Finset.mem_filter.mp hA).2.2)]
  rfl

@[simp] theorem ursell_empty {V : Type*} [LinearOrder V] (I : SimpleGraph V) : ursell I ∅ = 0 := by
  rw [ursell, WellFounded.fix_eq,
    dite_eq_right (by simp : ¬ (∅ : Finset V).Nonempty)]

/-- 单元素集合：`φ({i}) = 1`（`(2.2)` 中 filter 为空）。 -/
theorem ursell_singleton {V : Type*} [LinearOrder V] (I : SimpleGraph V) (i : V) :
    ursell I {i} = 1 := by
  have hne : ({i} : Finset V).Nonempty := ⟨i, Finset.mem_singleton_self i⟩
  rw [ursell_eq_of_nonempty I hne]
  have hmin : ({i} : Finset V).min' hne = i := Finset.min'_singleton i
  have hempty : ({i} : Finset V).powerset.filter
      (fun T => ({i} : Finset V).min' hne ∈ T ∧ T ≠ ({i} : Finset V)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro T hT
    rw [Finset.mem_powerset] at hT
    rcases Finset.subset_singleton_iff.mp hT with h | h <;> simp [h, hmin]
  rw [hempty, Finset.sum_empty]
  simp [compatInd, isCompatible_singleton]

/-- 二元集合上的 `(2.2)`：filter 恰是单点集 `{min S}`，故 `φ(S) = [S 相容] − 1`。 -/
private theorem ursell_of_card_two {V : Type*} [LinearOrder V] (I : SimpleGraph V) {S : Finset V}
    (hcard : S.card = 2) : ursell I S = compatInd I S - 1 := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hmin : S.min' hne ∈ S := Finset.min'_mem S hne
  rw [ursell_eq_of_nonempty I hne]
  have hsum : ∑ A ∈ S.powerset.filter (fun T => S.min' hne ∈ T ∧ T ≠ S),
        ursell I A * compatInd I (S \ A)
      = ursell I {S.min' hne} * compatInd I (S \ {S.min' hne}) := by
    refine Finset.sum_eq_single ({S.min' hne} : Finset V) ?_ ?_
    · intro A hA hne'
      exfalso
      rw [Finset.mem_filter, Finset.mem_powerset] at hA
      obtain ⟨hsub, hmA, hAS⟩ := hA
      have hle : A.card ≤ 2 := by
        calc A.card ≤ S.card := Finset.card_le_card hsub
        _ = 2 := hcard
      have hpos : 0 < A.card := Finset.card_pos.mpr ⟨_, hmA⟩
      have hne1 : A.card ≠ 1 := by
        intro h1
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
        have : a = S.min' hne := by
          rw [ha] at hmA
          exact (Finset.mem_singleton.mp hmA).symm
        exact hne' (by rw [ha, this])
      have hne2 : A.card ≠ 2 := by
        intro h2
        exact hAS (Finset.eq_of_subset_of_card_le hsub (by omega))
      omega
    · intro h
      refine absurd ?_ h
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.singleton_subset_iff.mpr hmin, Finset.mem_singleton_self _,
        fun hEq => by rw [← hEq] at hcard; simp at hcard⟩
  rw [hsum, ursell_singleton I]
  have hcomp : compatInd I (S \ {S.min' hne}) = 1 := by
    have hc : (S \ {S.min' hne}).card = 1 := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hmin, hcard]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    rw [ha]
    simp [compatInd, isCompatible_singleton]
  rw [hcomp, mul_one]

/-- 二元组：不相容 ⇒ `φ = −1`（CE0/CE1 的 `n = 2` 读数）。 -/
theorem ursell_pair_eq_neg_one {V : Type*} [LinearOrder V] (I : SimpleGraph V) {i j : V}
    (hij : i ≠ j) (hadj : I.Adj i j) : ursell I {i, j} = -1 := by
  have hcard : ({i, j} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
  rw [ursell_of_card_two I hcard]
  have hnot : ¬ IsCompatible I ({i, j} : Finset V) :=
    fun h => h i (by simp) j (by simp) hij hadj
  have : compatInd I ({i, j} : Finset V) = 0 := by simp [compatInd, hnot]
  rw [this]
  ring

/-- **`(2.2)` 的更新方程**（CE0 交叉验证的那条恒等式）：
`[S 相容] = Σ_{A ∋ min S, A ⊆ S} φ(A)·[S∖A 相容]`（含 `A = S` 项）。 -/
theorem compatInd_eq_sum {V : Type*} [LinearOrder V] (I : SimpleGraph V) {S : Finset V}
    (hS : S.Nonempty) :
    compatInd I S = ∑ A ∈ S.powerset.filter (fun A => S.min' hS ∈ A),
        ursell I A * compatInd I (S \ A) := by
  have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
  have hrec := ursell_eq_of_nonempty I hS
  have hfil : S.powerset.filter (fun A => S.min' hS ∈ A ∧ A ≠ S)
      = (S.powerset.filter (fun A => S.min' hS ∈ A)).erase S := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
    tauto
  have hmem : S ∈ S.powerset.filter (fun A => S.min' hS ∈ A) := by
    simp [Finset.mem_powerset, hmin]
  have hsum := Finset.sum_erase_add (s := S.powerset.filter (fun A => S.min' hS ∈ A))
    (f := fun A => ursell I A * compatInd I (S \ A)) hmem
  have hsub : ∑ A ∈ (S.powerset.filter (fun A => S.min' hS ∈ A)).erase S,
        ursell I A * compatInd I (S \ A)
      = (∑ A ∈ S.powerset.filter (fun A => S.min' hS ∈ A),
          ursell I A * compatInd I (S \ A)) - ursell I S * compatInd I (S \ S) := by
    linarith [hsum]
  rw [hfil, hsub, Finset.sdiff_self, compatInd_empty, mul_one] at hrec
  linarith

/-! ### §3 引理 3.1 的一个真情形：无边 ⇒ `φ = 0` -/

/-- **引理 3.1 的"无边 ⇒ 0"情形**：`S` 完全相容（`𝕀(S)` 无边）且 `|S| ≥ 2` ⇒ `φ(S) = 0`。

证明：对 `S` 作强归纳（`⊂`）。`(2.2)` 的 filter 里每一项都是含 `min S` 的 `S` 的真子集，
于是只剩两块：`A = {min S}`（贡献 `φ({min S})·[S∖{min S} 相容] = 1`）与其余
（`|A| ≥ 2`、`A ⊊ S`、`A ⊆ S` 相容 ⇒ 归纳假设给 `φ(A) = 0`）。和恰为 `1`，
而 `[S 相容] = 1` ⇒ `φ(S) = 0`。 -/
theorem ursell_eq_zero_of_compatible {V : Type*} [LinearOrder V] (I : SimpleGraph V) :
    ∀ S : Finset V, IsCompatible I S → 2 ≤ S.card → ursell I S = 0 := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hcomp hcard
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    rw [ursell_eq_of_nonempty I hSne]
    have hcompInd : compatInd I S = 1 := by simp [compatInd, hcomp]
    have hmin : S.min' hSne ∈ S := Finset.min'_mem S hSne
    have hsum : ∑ A ∈ S.powerset.filter (fun T => S.min' hSne ∈ T ∧ T ≠ S),
          ursell I A * compatInd I (S \ A)
        = ursell I {S.min' hSne} * compatInd I (S \ {S.min' hSne}) := by
      refine Finset.sum_eq_single ({S.min' hSne} : Finset V) ?_ ?_
      · intro A hA hne'
        rw [Finset.mem_filter, Finset.mem_powerset] at hA
        obtain ⟨hsub, hmA, hAS⟩ := hA
        have hlt : A ⊂ S := lt_of_le_of_ne hsub hAS
        have hne1 : A.card ≠ 1 := by
          intro h1
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
          have : a = S.min' hSne := by
            rw [ha] at hmA
            exact (Finset.mem_singleton.mp hmA).symm
          exact hne' (by rw [ha, this])
        have hge : 2 ≤ A.card := by
          have hpos : 0 < A.card := Finset.card_pos.mpr ⟨_, hmA⟩
          omega
        rw [ih A hlt (hcomp.mono hsub) hge, zero_mul]
      · intro h
        refine absurd ?_ h
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.singleton_subset_iff.mpr hmin, Finset.mem_singleton_self _,
          fun hEq => by rw [← hEq] at hcard; simp at hcard⟩
    rw [hsum, hcompInd]
    have hsub : IsCompatible I (S \ {S.min' hSne}) := hcomp.mono Finset.sdiff_subset
    have hsubInd : compatInd I (S \ {S.min' hSne}) = 1 := by simp [compatInd, hsub]
    rw [hsubInd, ursell_singleton I (S.min' hSne), one_mul]
    ring

end Pphi2Ursell
