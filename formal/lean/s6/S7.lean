import Mathlib

/-!
# S7 — Polarisation of symmetric multilinear forms

Paper `lem:polarisation` (eq:polarisation) and `cor:diagonal`: a symmetric `n`-linear form
is determined by its diagonal values, via
`Φ f = (n!)⁻¹ * ∑_{S ⊆ [n]} (-1)^{n-|S|} Φ(g_S, …, g_S)`, `g_S = ∑_{i∈S} f_i`.
-/

noncomputable section

open scoped BigOperators

namespace Schwinger

open Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Symmetry of an `n`-linear form: invariant under reindexing by a permutation. -/
def IsSymmMultilinear {n : ℕ} (Φ : MultilinearMap ℝ (fun _ : Fin n => E) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), Φ (v ∘ σ) = Φ v

/-- `(-1)^(a-b) = (-1)^a * (-1)^b` for `b ≤ a`. -/
lemma neg_one_pow_sub (a b : ℕ) (hb : b ≤ a) :
    (-1 : ℝ) ^ (a - b) = (-1 : ℝ) ^ a * (-1 : ℝ) ^ b := by
  have hsq : (-1 : ℝ) ^ b * (-1 : ℝ) ^ b = 1 := by
    rw [← pow_add, show b + b = 2 * b from by ring, pow_mul]
    norm_num
  calc (-1 : ℝ) ^ (a - b) = (-1 : ℝ) ^ (a - b) * ((-1 : ℝ) ^ b * (-1 : ℝ) ^ b) := by
        rw [hsq, mul_one]
    _ = (-1 : ℝ) ^ ((a - b) + b) * (-1 : ℝ) ^ b := by rw [pow_add]; ring
    _ = (-1 : ℝ) ^ a * (-1 : ℝ) ^ b := by rw [Nat.sub_add_cancel hb]

/-- The alternating sum over the subsets of a finite set: `∑_{R ⊆ x} (-1)^{|R|}`. -/
lemma sum_powerset_neg_one_pow_card_real {α : Type*} [DecidableEq α] (x : Finset α) :
    (∑ R ∈ x.powerset, (-1 : ℝ) ^ R.card) = if x = ∅ then 1 else 0 := by
  have hcast : (∑ R ∈ x.powerset, (-1 : ℝ) ^ R.card)
      = ((∑ R ∈ x.powerset, (-1 : ℤ) ^ R.card : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    exact sum_congr rfl fun R _ => by rw [Int.cast_pow]; norm_num
  rw [hcast, Finset.sum_powerset_neg_one_pow_card]
  split <;> norm_num

/-- Superset form of the alternating sum: for `T ⊆ U`,
`∑_{T ⊆ S ⊆ U} (-1)^{|U|-|S|} = if T = U then 1 else 0`. -/
lemma sum_powerset_supset_neg_one {n : ℕ} (U T : Finset (Fin n)) (hTU : T ⊆ U) :
    (∑ S ∈ U.powerset.filter (fun S => T ⊆ S), (-1 : ℝ) ^ (U.card - S.card))
      = if T = U then 1 else 0 := by
  have key : (∑ S ∈ U.powerset.filter (fun S => T ⊆ S), (-1 : ℝ) ^ (U.card - S.card))
      = ∑ R ∈ (U \ T).powerset,
          (-1 : ℝ) ^ (U.card - T.card) * (-1 : ℝ) ^ R.card := by
    refine Finset.sum_bij (fun S _ => S \ T) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hS.1 le_rfl)
    · intro S₁ hS₁ S₂ hS₂ heq
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS₁ hS₂
      have h1 : S₁ = T ∪ (S₁ \ T) := (Finset.union_sdiff_of_subset hS₁.2).symm
      have h2 : S₂ = T ∪ (S₂ \ T) := (Finset.union_sdiff_of_subset hS₂.2).symm
      rw [h1, h2, heq]
    · intro R hR
      simp only [Finset.mem_powerset] at hR
      refine ⟨T ∪ R, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset hTU (hR.trans Finset.sdiff_subset), Finset.subset_union_left⟩
      · have hdisj : Disjoint R T := by
          rw [Finset.disjoint_left]
          intro a haR haT
          exact (Finset.mem_sdiff.mp (hR haR)).2 haT
        rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint.mpr hdisj]
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      have hdisj : Disjoint T (S \ T) := by
        rw [Finset.disjoint_left]; intro a ha hb; exact (Finset.mem_sdiff.mp hb).2 ha
      have hcard : S.card = T.card + (S \ T).card := by
        conv_lhs => rw [← Finset.union_sdiff_of_subset hS.2]
        rw [Finset.card_union_of_disjoint hdisj]
      have hle : (S \ T).card ≤ U.card - T.card := by
        have h1 : (S \ T).card ≤ (U \ T).card :=
          Finset.card_le_card (Finset.sdiff_subset_sdiff hS.1 le_rfl)
        have h2 : (U \ T).card + T.card = U.card := Finset.card_sdiff_add_card_eq_card hTU
        omega
      rw [hcard, ← Nat.sub_sub, neg_one_pow_sub (U.card - T.card) (S \ T).card hle]
  rw [key, ← Finset.mul_sum, sum_powerset_neg_one_pow_card_real]
  by_cases h : T = U
  · subst h; simp
  · rw [if_neg h]
    have hne : U \ T ≠ ∅ := by
      simp only [ne_eq, Finset.sdiff_eq_empty_iff_subset]
      intro hUT
      exact h (Finset.Subset.antisymm hTU hUT)
    rw [if_neg hne, mul_zero]

/-- **Polarisation identity** (paper `lem:polarisation`, eq:polarisation). -/
theorem polarization {n : ℕ} (Φ : MultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (hΦ : IsSymmMultilinear Φ) (f : Fin n → E) :
    Φ f = (n.factorial : ℝ)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (-1 : ℝ) ^ (n - S.card) * Φ (fun _ => ∑ i ∈ S, f i) := by
  classical
  set U : Finset (Fin n) := Finset.univ with hU
  have hUcard : U.card = n := by simp [hU]
  set F : Finset (Fin n → Fin n) := Fintype.piFinset (fun _ : Fin n => U) with hF
  have key : (∑ S ∈ U.powerset, (-1 : ℝ) ^ (U.card - S.card) * Φ (fun _ => ∑ i ∈ S, f i))
      = (n.factorial : ℝ) * Φ f := by
    have step1 : (∑ S ∈ U.powerset,
          (-1 : ℝ) ^ (U.card - S.card) * Φ (fun _ => ∑ i ∈ S, f i))
        = ∑ S ∈ U.powerset, (-1 : ℝ) ^ (U.card - S.card) *
            (∑ r ∈ Fintype.piFinset (fun _ : Fin n => S), Φ (fun i => f (r i))) := by
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [MultilinearMap.map_sum_finset (g := fun _ i => f i) (A := fun _ : Fin n => S)]
    rw [step1]
    have step2 : (∑ S ∈ U.powerset, (-1 : ℝ) ^ (U.card - S.card) *
            (∑ r ∈ Fintype.piFinset (fun _ : Fin n => S), Φ (fun i => f (r i))))
        = ∑ S ∈ U.powerset, ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S),
            (-1 : ℝ) ^ (U.card - S.card) * Φ (fun i => f (r i)) := by
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.mul_sum]
    rw [step2]
    have step3 : ∀ S ∈ U.powerset,
        (∑ r ∈ Fintype.piFinset (fun _ : Fin n => S),
            (-1 : ℝ) ^ (U.card - S.card) * Φ (fun i => f (r i)))
        = ∑ r ∈ F, (if r ∈ Fintype.piFinset (fun _ : Fin n => S) then
            (-1 : ℝ) ^ (U.card - S.card) * Φ (fun i => f (r i)) else 0) := by
      intro S _
      rw [← Finset.sum_subset
            (show Fintype.piFinset (fun _ : Fin n => S) ⊆ F from fun r _ =>
              by simp only [hF, Fintype.mem_piFinset]; exact fun _ => Finset.mem_univ _)
            (show ∀ r ∈ F, r ∉ Fintype.piFinset (fun _ : Fin n => S) →
                (if r ∈ Fintype.piFinset (fun _ : Fin n => S) then
                  (-1 : ℝ) ^ (U.card - S.card) * Φ (fun i => f (r i)) else 0) = 0 from
              fun r _ hr => if_neg hr)]
      exact Finset.sum_congr rfl fun r hr => (if_pos hr).symm
    rw [show (∑ S ∈ U.powerset, ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S),
            (-1 : ℝ) ^ (U.card - S.card) * Φ (fun i => f (r i)))
          = ∑ S ∈ U.powerset, ∑ r ∈ F, (if r ∈ Fintype.piFinset (fun _ : Fin n => S) then
            (-1 : ℝ) ^ (U.card - S.card) * Φ (fun i => f (r i)) else 0) from
        Finset.sum_congr rfl fun S hS => step3 S hS]
    rw [Finset.sum_comm]
    have step5 : ∀ r ∈ F, (∑ S ∈ U.powerset,
          (if r ∈ Fintype.piFinset (fun _ : Fin n => S) then
            (-1 : ℝ) ^ (U.card - S.card) * Φ (fun i => f (r i)) else 0))
        = (∑ S ∈ U.powerset.filter (fun S => Finset.image r U ⊆ S),
              (-1 : ℝ) ^ (U.card - S.card)) * Φ (fun i => f (r i)) := by
      intro r _
      rw [← Finset.sum_filter, Finset.sum_mul]
      congr 1
      apply Finset.filter_congr
      intro S _
      rw [Fintype.mem_piFinset]
      exact ⟨fun h a ha => by
              obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha; exact h i,
            fun h i => h (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
    have step6 : ∀ r ∈ F, (∑ S ∈ U.powerset.filter (fun S => Finset.image r U ⊆ S),
              (-1 : ℝ) ^ (U.card - S.card)) = if Finset.image r U = U then 1 else 0 := by
      intro r _
      exact sum_powerset_supset_neg_one U (Finset.image r U) (fun a _ => Finset.mem_univ a)
    rw [show (∑ r ∈ F, (∑ S ∈ U.powerset, (if r ∈ Fintype.piFinset (fun _ : Fin n => S) then
            (-1 : ℝ) ^ (U.card - S.card) * Φ (fun i => f (r i)) else 0)))
          = ∑ r ∈ F, (if Finset.image r U = U then 1 else 0) * Φ (fun i => f (r i)) from
        Finset.sum_congr rfl fun r hr => by rw [step5 r hr, step6 r hr]]
    have hite : ∀ (c : Prop) [Decidable c] (x : ℝ),
        (if c then (1 : ℝ) else 0) * x = if c then x else 0 := by
      intro c _ x; by_cases h : c <;> simp [h]
    simp_rw [hite]
    rw [← Finset.sum_filter]
    have hF_eq : F = (Finset.univ : Finset (Fin n → Fin n)) := by
      ext r; simp only [hF, Fintype.mem_piFinset, Finset.mem_univ, iff_true]
      exact fun _ => Finset.mem_univ _
    rw [hF_eq]
    have hpred : (Finset.univ : Finset (Fin n → Fin n)).filter
          (fun r => Finset.image r U = U)
        = (Finset.univ : Finset (Fin n → Fin n)).filter (fun r => Function.Surjective r) := by
      apply Finset.filter_congr
      intro r _
      rw [hU]
      exact ⟨fun h => by
              intro a
              have : a ∈ Finset.image r (Finset.univ : Finset (Fin n)) := by
                rw [h]; exact Finset.mem_univ a
              obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this
              exact ⟨i, hi⟩,
            fun h => Finset.image_univ_of_surjective h⟩
    rw [hpred]
    rw [show (∑ r ∈ (Finset.univ : Finset (Fin n → Fin n)).filter
            (fun r => Function.Surjective r), Φ (fun i => f (r i)))
          = ∑ σ : Equiv.Perm (Fin n), Φ (fun i => f (σ i)) from by
        refine Finset.sum_bij
          (fun r hr => Equiv.ofBijective (r : Fin n → Fin n)
            (show Function.Bijective (r : Fin n → Fin n) from
              ⟨(Finite.injective_iff_surjective).mpr ((Finset.mem_filter.mp hr).2),
               (Finset.mem_filter.mp hr).2⟩)) ?_ ?_ ?_ ?_
        · intro r _; exact Finset.mem_univ _
        · intro r₁ hr₁ r₂ hr₂ heq
          funext i
          have h3 := congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) heq) i
          rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply] at h3
          exact h3
        · intro σ _
          refine ⟨(σ : Fin n → Fin n), ?_, ?_⟩
          · rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, σ.surjective⟩
          · ext i; rw [Equiv.ofBijective_apply]
        · intro r _
          rfl]
    rw [show (∑ σ : Equiv.Perm (Fin n), Φ (fun i => f (σ i)))
          = ∑ _σ : Equiv.Perm (Fin n), Φ f from
        Finset.sum_congr rfl fun σ _ => hΦ σ f]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp [nsmul_eq_mul]
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hgoal : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (-1 : ℝ) ^ (n - S.card) * Φ (fun _ => ∑ i ∈ S, f i))
      = (n.factorial : ℝ) * Φ f := by
    have hkey := key
    rw [hUcard] at hkey
    rw [hU] at hkey
    exact hkey
  rw [hgoal, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

/-- **Diagonal values determine a symmetric multilinear form** (paper `cor:diagonal`). -/
theorem eq_of_diagonal_eq {n : ℕ} (Φ Ψ : MultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (hΦ : IsSymmMultilinear Φ) (hΨ : IsSymmMultilinear Ψ)
    (h : ∀ g : E, Φ (fun _ => g) = Ψ (fun _ => g)) : Φ = Ψ := by
  ext f
  rw [polarization Φ hΦ f, polarization Ψ hΨ f]
  congr 1
  exact Finset.sum_congr rfl fun S _ => by rw [h]

end Schwinger
