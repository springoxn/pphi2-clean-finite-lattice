import AImathPPhi2Clean.Periodic3DCarrierEnergy
import AImathPPhi2Clean.Periodic3DCompactEmbedding
import AImathPPhi2Clean.Periodic3DGaussianPushforward
import Mathlib.MeasureTheory.Measure.Prokhorov

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

theorem periodic3DFiniteSourceFourierLiftH3_norm_eq
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    ‖periodic3DFiniteSourceFourierLiftH3 N a L ω‖ =
      periodic3DHminusThreeNorm (periodic3DRawAtomicLift N a L hL ω) := by
  rw [← Real.sqrt_sq (norm_nonneg _), periodic3DFiniteSourceFourierLiftH3_norm_sq N a L ha hL]
  rfl

theorem periodic3DFiniteSourceFourierLift_mem_three_ball
    (N : ℕ) [NeZero N] (a L B : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)))
    (hB : ‖periodic3DFiniteSourceFourierLiftH3 N a L ω‖ ≤ B) :
    periodic3DFiniteSourceFourierLift N a L ω ∈ periodic3DHminusThreeBallInHminusFour B := by
  refine ⟨periodic3DRawAtomicLift N a L hL ω,
    periodic3DRawAtomicLift_mem_carrier_three N a L ha hL ω, ?_, ?_⟩
  · rwa [← periodic3DFiniteSourceFourierLiftH3_norm_eq N a L ha hL]
  · apply lp.ext
    funext k
    exact (congrFun (periodic3DRawWeightedLift_eq_finiteSourceFourierLift N a L ha hL ω) k).symm

theorem periodic3DFiniteSourceGaussianMeasure_compactTail
    (N : ℕ) [NeZero N] (a mass L B : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) (hB : 0 < B) :
    periodic3DFiniteSourceGaussianMeasure N a mass L ha hmass
      (closure (periodic3DHminusThreeBallInHminusFour B))ᶜ ≤
      ENNReal.ofReal ((2 * (mass⁻¹ ^ 2 * L ^ 3) *
        ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k) / B ^ 2) := by
  let μ := finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)
  let X := periodic3DFiniteSourceFourierLiftH3 N a L
  let Y := periodic3DFiniteSourceFourierLift N a L
  let K : Set Periodic3DCompletion := closure (periodic3DHminusThreeBallInHminusFour B)
  have hKcompact : IsCompact K := isCompact_closure_periodic3DHminusThreeBall B hB.le
  have hpre : Y ⁻¹' Kᶜ ⊆ {ω | B ^ 2 ≤ ‖X ω‖ ^ 2} := by
    intro ω hω
    by_contra htail
    have hnorm : ‖X ω‖ ≤ B := by
      have hh : ‖X ω‖ ^ 2 < B ^ 2 := lt_of_not_ge htail
      nlinarith [norm_nonneg (X ω)]
    exact hω (subset_closure (periodic3DFiniteSourceFourierLift_mem_three_ball N a L B ha hL ω hnorm))
  rw [periodic3DFiniteSourceGaussianMeasure_apply N a mass L ha hmass Kᶜ
    hKcompact.isClosed.measurableSet.compl]
  exact (measure_mono hpre).trans
    (periodic3DFiniteSourceFourierLiftH3_markov_tail N a mass L B ha hmass hvol hL hB)

def periodic3DFixedVolumeProbabilityMeasure
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    ProbabilityMeasure Periodic3DCompletion := by
  let N := n + 1
  let a : ℝ := L / ((n + 1 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hNa : a * (N : ℝ) = L := by
    dsimp [a, N]
    field_simp
  exact ⟨periodic3DFiniteSourceGaussianMeasure N a mass L ha hmass,
    inferInstance⟩
theorem periodic3DFixedVolumeProbabilityMeasureSet_tight
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    IsTightMeasureSet
      {ρ : Measure Periodic3DCompletion |
        ∃ n, ρ = (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass n : Measure _) } := by
  refine (isTightMeasureSet_iff_exists_isCompact_measure_compl_le).2 ?_
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ρ hρ
    simp [htop]
  · have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    let er : ℝ := ε.toReal
    let C : ℝ := 2 * (mass⁻¹ ^ 2 * L ^ 3) *
      ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k
    let D : ℝ := C + 1
    let B : ℝ := Real.sqrt (D / er)
    have hsum : 0 ≤ ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k :=
      tsum_nonneg (fun k => periodic3DHminusThreeWeight_nonneg k)
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hD : 0 < D := by dsimp [D]; linarith
    have her : 0 < er := hεreal
    have hB : 0 < B := by
      dsimp [B]
      exact Real.sqrt_pos.2 (div_pos hD her)
    refine ⟨closure (periodic3DHminusThreeBallInHminusFour B),
      isCompact_closure_periodic3DHminusThreeBall B hB.le, ?_⟩
    intro ρ hρ
    rcases hρ with ⟨n, rfl⟩
    dsimp [periodic3DFixedVolumeProbabilityMeasure]
    let N := n + 1
    let a : ℝ := L / ((n + 1 : ℕ) : ℝ)
    have ha : 0 < a := by
      dsimp [a]
      exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
    have hNa : a * (N : ℝ) = L := by
      dsimp [a, N]
      field_simp
    have htail := periodic3DFiniteSourceGaussianMeasure_compactTail
      N a mass L B ha hmass hNa hL hB
    rw [← ENNReal.ofReal_toReal htop]
    have hBsq : B ^ 2 = D / er := by
      dsimp [B]
      rw [Real.sq_sqrt (le_of_lt (div_pos hD her))]
    have hreal : C / B ^ 2 ≤ er := by
      rw [hBsq]
      dsimp [D]
      have her0 : 0 ≤ er := her.le
      have hden : 0 < C + 1 := by linarith
      apply (div_le_iff₀ (div_pos (by linarith : 0 < C + 1) her)).2
      field_simp
      nlinarith
    exact htail.trans (ENNReal.ofReal_le_ofReal hreal)
open Filter
open scoped Topology
theorem periodic3DFixedVolume_prokhorov_subsequence
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop) :
    ∃ (ms : ℕ → ℕ) (ν : ProbabilityMeasure Periodic3DCompletion),
      StrictMono ms ∧
      Tendsto
        (fun k => periodic3DFixedVolumeProbabilityMeasure L mass hL hmass (ns (ms k)))
        atTop (𝓝 ν) := by
  letI : TopologicalSpace.SeparableSpace Periodic3DCompletion :=
    periodic3DHminusFourCompletion_separable
  let μ : ℕ → ProbabilityMeasure Periodic3DCompletion :=
    periodic3DFixedVolumeProbabilityMeasure L mass hL hmass
  let S : Set (ProbabilityMeasure Periodic3DCompletion) := Set.range μ
  have htight : IsTightMeasureSet
      {ρ : Measure Periodic3DCompletion | ∃ n, ρ = (μ n : Measure _)} := by
    simpa [μ] using periodic3DFixedVolumeProbabilityMeasureSet_tight L mass hL hmass
  have hcompact : IsCompact (closure S) := by
    apply isCompact_closure_of_isTightMeasureSet
    simpa [S, Set.ext_iff, eq_comm] using htight
  have hseq : ∀ n, μ (ns n) ∈ closure S := by
    intro n
    exact subset_closure ⟨ns n, rfl⟩
  obtain ⟨ν, _hνS, ms, hms, hlim⟩ := hcompact.tendsto_subseq hseq
  refine ⟨ms, ν, hms, ?_⟩
  simpa [Function.comp_def, μ] using hlim
end Pphi2Clean.Continuum
