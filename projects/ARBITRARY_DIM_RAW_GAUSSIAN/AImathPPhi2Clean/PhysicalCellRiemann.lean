import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open scoped Topology Pointwise
open MeasureTheory BoxIntegral
namespace Pphi2Clean.Continuum

open scoped Classical in
/-- Retag the standard uniform mesh at lower vertices. -/
def lowerUnitPartition {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (B : Box ι) : TaggedPrepartition B where
  toPrepartition := (unitPartition.prepartition N B).toPrepartition
  tag J := if J ≤ B then J.lower else B.lower
  tag_mem_Icc J := by
    classical
    split_ifs with h
    · exact Box.le_iff_Icc.mp h J.lower_mem_Icc
    · exact B.lower_mem_Icc

theorem lowerUnitPartition_tag {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (B J : Box ι) (hJ : J ∈ unitPartition.prepartition N B) :
    (lowerUnitPartition N B).tag J = J.lower := by
  classical
  exact if_pos ((unitPartition.prepartition N B).le_of_mem hJ)

theorem lowerUnitPartition_isHenstock {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (B : Box ι) : (lowerUnitPartition N B).IsHenstock := by
  intro J hJ
  rw [lowerUnitPartition_tag N B J hJ]
  exact J.lower_mem_Icc

theorem lowerUnitPartition_isSubordinate {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (B : Box ι) {r : ℝ} (hr : 0 < r) (hN : 1 / (N : ℝ) ≤ r) :
    (lowerUnitPartition N B).IsSubordinate (fun _ => ⟨r, hr⟩) := by
  intro J hJ
  have hmem : J ∈ unitPartition.prepartition N B := hJ
  rw [lowerUnitPartition_tag N B J hmem]
  obtain ⟨ν, hν, rfl⟩ := unitPartition.mem_prepartition_iff.mp hmem
  intro x hx
  exact (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _) hx (Box.lower_mem_Icc _)).trans
    ((unitPartition.diam_boxIcc N ν).trans hN)

/-- Lower-vertex mesh sums converge to the actual Bochner volume integral.
The statement holds for an arbitrary Banach-valued continuous integrand. -/
theorem lowerUnitPartition_integralSum_tendsto
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (B : Box ι) (hB : hasIntegralVertices B) (f : (ι → ℝ) → E)
    (hf : ContinuousOn f (Box.Icc B)) :
    Filter.Tendsto (fun n : ℕ => integralSum f
      (volume : Measure (ι → ℝ)).toBoxAdditive.toSMul (lowerUnitPartition (n + 1) B))
      Filter.atTop (nhds (∫ x in B, f x)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨r, hr₁, hr₂⟩ := (hasIntegral_iff.mp <|
    hf.hasBoxIntegral (volume : Measure (ι → ℝ)) IntegrationParams.Riemann)
      (ε / 2) (half_pos hε)
  refine ⟨⌈(r 0 0 : ℝ)⁻¹⌉₊, ?_⟩
  intro n hn
  apply lt_of_le_of_lt ?_ (half_lt_self_iff.mpr hε)
  apply hr₂ 0 (lowerUnitPartition (n + 1) B) ?_
    (unitPartition.prepartition_isPartition (n + 1) hB)
  refine ⟨?_, fun _ => lowerUnitPartition_isHenstock (n + 1) B, ?_, ?_⟩
  · rw [show r 0 = fun _ => r 0 0 from funext_iff.mpr (hr₁ 0 rfl)]
    apply lowerUnitPartition_isSubordinate (n + 1) B
    rw [one_div, inv_le_comm₀ (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) (r 0 0).prop]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ n).trans' hn)
  · intro h
    simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h
  · intro h
    simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h

/-- Unit physical coordinate box, including the empty coordinate type. -/
def physicalUnitBox (ι : Type*) : Box ι :=
  ⟨fun _ => 0, fun _ => 1, fun _ => zero_lt_one⟩

theorem physicalUnitBox_hasIntegralVertices (ι : Type*) :
    hasIntegralVertices (physicalUnitBox ι) :=
  ⟨fun _ => 0, fun _ => 1, fun _ => by simp [physicalUnitBox], fun _ => by simp [physicalUnitBox]⟩

theorem mem_unit_admissibleIndex_iff {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N] (ν : ι → ℤ) :
    ν ∈ unitPartition.admissibleIndex N (physicalUnitBox ι) ↔
      ∀ i, 0 ≤ ν i ∧ ν i < (N : ℤ) := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  rw [unitPartition.mem_admissibleIndex_iff, Box.le_iff_bounds]
  simp only [physicalUnitBox, unitPartition.box_lower, unitPartition.box_upper, Pi.le_def]
  constructor
  · intro ⟨hl, hu⟩ i
    have hli : (0 : ℝ) ≤ (ν i : ℝ) := by
      simpa using (le_div_iff₀ hN).mp (hl i)
    have hui : (ν i : ℝ) + 1 ≤ (N : ℝ) := (div_le_one hN).mp (hu i)
    constructor
    · exact_mod_cast hli
    · have : ν i + 1 ≤ (N : ℤ) := by exact_mod_cast hui
      omega
  · intro h
    constructor
    · intro i
      exact div_nonneg (by exact_mod_cast (h i).1) hN.le
    · intro i
      apply (div_le_one hN).mpr
      have hi := (h i).2
      have : ν i + 1 ≤ (N : ℤ) := by omega
      exact_mod_cast this

/-- Exact lower-mesh quadrature weight and finite grid indexing. -/
theorem lowerUnitPartition_integralSum_eq
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) [NeZero N] (f : (ι → ℝ) → E) :
    integralSum f (volume : Measure (ι → ℝ)).toBoxAdditive.toSMul
      (lowerUnitPartition N (physicalUnitBox ι)) =
      (1 / (N : ℝ)) ^ Fintype.card ι •
        ∑ q : ι → Fin N, f (fun i => ((q i).val : ℝ) / (N : ℝ)) := by
  classical
  unfold integralSum
  change (∑ J ∈ (unitPartition.prepartition N (physicalUnitBox ι)).boxes,
    (volume : Measure (ι → ℝ)).toBoxAdditive.toSMul J
      (f ((lowerUnitPartition N (physicalUnitBox ι)).tag J))) = _
  change (∑ J ∈ (unitPartition.admissibleIndex N (physicalUnitBox ι)).image (unitPartition.box N), _) = _
  rw [Finset.sum_image]
  · have htag (ν : ι → ℤ) (hν : ν ∈ unitPartition.admissibleIndex N (physicalUnitBox ι)) :
        (lowerUnitPartition N (physicalUnitBox ι)).tag (unitPartition.box N ν) =
          (fun i => (ν i : ℝ) / (N : ℝ)) := by
      exact lowerUnitPartition_tag N _ _ (unitPartition.mem_prepartition_iff.mpr ⟨ν, hν, rfl⟩)
    simp_rw [BoxAdditiveMap.toSMul_apply, Box.volume_apply,
      unitPartition.box.upper_sub_lower, Finset.prod_const, Finset.card_univ]
    rw [← Finset.smul_sum]
    congr 1
    symm
    apply Finset.sum_bij (fun (q : ι → Fin N) _ => fun i => ((q i).val : ℤ))
    · intro q hq
      rw [mem_unit_admissibleIndex_iff]
      intro i
      exact ⟨by positivity, by exact_mod_cast (q i).isLt⟩
    · intro q hq r hr heq
      funext i
      apply Fin.ext
      have := congrFun heq i
      exact_mod_cast this
    · intro ν hν
      have hv := (mem_unit_admissibleIndex_iff N ν).mp hν
      let q : ι → Fin N := fun i => ⟨(ν i).toNat, by
        have : ((ν i).toNat : ℤ) < (N : ℤ) := by rw [Int.toNat_of_nonneg (hv i).1]; exact (hv i).2
        exact_mod_cast this⟩
      refine ⟨q, Finset.mem_univ _, ?_⟩
      funext i
      exact Int.toNat_of_nonneg (hv i).1
    · intro q hq
      rw [htag _ ((mem_unit_admissibleIndex_iff N _).mpr (fun i =>
        ⟨by positivity, by exact_mod_cast (q i).isLt⟩))]
      simp
  · intro ν hν μ hμ heq
    exact unitPartition.box_injective N heq

/-- Uniform lower-vertex quadrature on the closed unit cube, with Lebesgue
volume and no probability normalization. -/
theorem unitCell_riemann_sum_tendsto
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (ι → ℝ) → E)
    (hf : ContinuousOn f (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1))) :
    Filter.Tendsto (fun n : ℕ =>
      (1 / ((n + 1 : ℕ) : ℝ)) ^ Fintype.card ι •
        ∑ q : ι → Fin (n + 1), f (fun i => ((q i).val : ℝ) / ((n + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds (∫ x in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1), f x)) := by
  have hbox : Box.Icc (physicalUnitBox ι) =
      Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    rw [Box.Icc_eq_pi]
    rfl
  have hh := lowerUnitPartition_integralSum_tendsto (physicalUnitBox ι)
    (physicalUnitBox_hasIntegralVertices ι) f (hbox ▸ hf)
  have heq : (∫ x in (physicalUnitBox ι : Set (ι → ℝ)), f x) =
      ∫ x in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1), f x := by
    rw [setIntegral_congr_set (Box.coe_ae_eq_Icc _), hbox]
  simpa only [lowerUnitPartition_integralSum_eq, heq] using hh

/-- Scale the lower-vertex quadrature to a cell of physical side length L. -/
theorem physicalCell_riemann_sum_tendsto
    (d : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : ℝ) (hL : 0 < L) (f : (Fin d → ℝ) → E) (hf : Continuous f) :
    Filter.Tendsto (fun n : ℕ =>
      (L / ((n + 1 : ℕ) : ℝ)) ^ d •
        ∑ q : Fin d → Fin (n + 1), f (fun i =>
          L / ((n + 1 : ℕ) : ℝ) * ((q i).val : ℝ)))
      Filter.atTop (nhds (∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) L), f x)) := by
  let U : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  let C : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) L)
  have hset : L • U = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [U, C, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc, Pi.smul_apply,
        smul_eq_mul] at hy ⊢
      intro i
      exact ⟨mul_nonneg hL.le (hy i).1, by nlinarith [(hy i).2]⟩
    · intro hx
      refine ⟨fun i => x i / L, ?_, ?_⟩
      · simp only [U, C, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc] at hx ⊢
        intro i
        exact ⟨div_nonneg (hx i).1 hL.le, (div_le_one hL).mpr (hx i).2⟩
      · ext i
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp [hL.ne']
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (Fin d → ℝ)) f U hL
  rw [hset] at hscale
  have hdim : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  rw [hdim] at hscale
  have hcont : Continuous (fun y : Fin d → ℝ => f (L • y)) := hf.comp (by fun_prop)
  have hh := (unitCell_riemann_sum_tendsto (fun y : Fin d → ℝ => f (L • y)) hcont.continuousOn).const_smul (L ^ d)
  have hint : L ^ d • (∫ x in U, f (L • x)) = ∫ x in C, f x := by
    rw [hscale, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hL.ne'), one_smul]
  simp only [Fintype.card_fin] at hh
  rw [hint] at hh
  convert hh using 1
  funext n
  rw [smul_smul]
  congr 1
  · rw [← mul_pow]
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro q hq
    congr 1
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring

end Pphi2Clean.Continuum
