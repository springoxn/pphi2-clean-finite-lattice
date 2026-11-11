import AImathPPhi2Clean.Periodic3DHminusThreeSourceTightness

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

def periodic3DFixedVolumeProbabilityMeasureH3
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
  exact ⟨periodic3DFiniteSourceGaussianMeasureH3 N a mass L ha hmass,
    inferInstance⟩
theorem periodic3DFixedVolumeProbabilityMeasureH3Set_tight
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    IsTightMeasureSet
      {ρ : Measure Periodic3DCompletion |
        ∃ n, ρ = (periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass n : Measure _) } := by
  refine (isTightMeasureSet_iff_exists_isCompact_measure_compl_le).2 ?_
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ρ hρ
    simp [htop]
  · have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    let er : ℝ := ε.toReal
    let C : ℝ := 2 * (mass⁻¹ ^ 2 * L ^ 3) *
      ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k
    let D : ℝ := C + 1
    let B : ℝ := Real.sqrt (D / er)
    have hsum : 0 ≤ ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k :=
      tsum_nonneg (fun k => periodic3DSobolevWeight_nonneg 2 k)
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hD : 0 < D := by dsimp [D]; linarith
    have her : 0 < er := hεreal
    have hB : 0 < B := by
      dsimp [B]
      exact Real.sqrt_pos.2 (div_pos hD her)
    refine ⟨closure (periodic3DHminusTwoBallInHminusThree B),
      isCompact_closure_periodic3DHminusTwoBall B hB.le, ?_⟩
    intro ρ hρ
    rcases hρ with ⟨n, rfl⟩
    dsimp [periodic3DFixedVolumeProbabilityMeasureH3]
    let N := n + 1
    let a : ℝ := L / ((n + 1 : ℕ) : ℝ)
    have ha : 0 < a := by
      dsimp [a]
      exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
    have hNa : a * (N : ℝ) = L := by
      dsimp [a, N]
      field_simp
    have htail := periodic3DFiniteSourceGaussianMeasureH3_compactTail
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
theorem periodic3DFixedVolumeH3_prokhorov_subsequence
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop) :
    ∃ (ms : ℕ → ℕ) (ν : ProbabilityMeasure Periodic3DCompletion),
      StrictMono ms ∧
      Tendsto
        (fun k => periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass (ns (ms k)))
        atTop (𝓝 ν) := by
  letI : TopologicalSpace.SeparableSpace Periodic3DCompletion :=
    periodic3DHminusFourCompletion_separable
  let μ : ℕ → ProbabilityMeasure Periodic3DCompletion :=
    periodic3DFixedVolumeProbabilityMeasureH3 L mass hL hmass
  let S : Set (ProbabilityMeasure Periodic3DCompletion) := Set.range μ
  have htight : IsTightMeasureSet
      {ρ : Measure Periodic3DCompletion | ∃ n, ρ = (μ n : Measure _)} := by
    simpa [μ] using periodic3DFixedVolumeProbabilityMeasureH3Set_tight L mass hL hmass
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
