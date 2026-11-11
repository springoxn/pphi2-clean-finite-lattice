import AImathPPhi2Clean.Periodic3DHminusTwoSourceEnergy
import AImathPPhi2Clean.Periodic3DHminusTwoBallCompactInHminusThree
import AImathPPhi2Clean.Periodic3DCarrierEnergy
import Mathlib.MeasureTheory.Measure.Prokhorov

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

theorem periodic3DFiniteSourceFourierLiftH2_markov_tail
    (N : ℕ) [NeZero N] (a mass L B : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) (hB : 0 < B) :
    finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)
      {ω | B ^ 2 ≤ ‖periodic3DFiniteSourceFourierLiftH2 N a L ω‖ ^ 2} ≤
      ENNReal.ofReal ((2 * (mass⁻¹ ^ 2 * L ^ 3) *
        ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k) / B ^ 2) := by
  let μ := finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 3 N a mass ha hmass)
  let X := periodic3DFiniteSourceFourierLiftH2 N a L
  have hInt := periodic3DFiniteSourceFourierLiftH2_integrable_norm_sq N a mass L ha hmass
  have hSecond := periodic3DFiniteSourceFourierLiftH2_integral_norm_sq_le
    N a mass L ha hmass hvol hL
  have hScaled : Integrable (fun ω => ‖X ω‖ ^ 2 / B ^ 2) μ := by
    have hmul := hInt.const_mul ((B ^ 2)⁻¹)
    convert hmul using 1
    ext ω
    simp [X, div_eq_mul_inv, mul_comm]
  have hNonneg : 0 ≤ᵐ[μ] (fun ω => ‖X ω‖ ^ 2 / B ^ 2) := by
    filter_upwards [] with ω
    exact div_nonneg (sq_nonneg ‖X ω‖) (sq_nonneg B)
  let s : Set (FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :=
    {ω | B ^ 2 ≤ ‖X ω‖ ^ 2}
  have hMarkov := hScaled.measure_le_integral hNonneg (s := s)
    (by
      intro ω hω
      dsimp [s] at hω ⊢
      exact (le_div_iff₀ (sq_pos_of_pos hB)).2 (by simpa using hω))
  have hIntegral : (∫ ω, ‖X ω‖ ^ 2 / B ^ 2 ∂μ) ≤
      (2 * (mass⁻¹ ^ 2 * L ^ 3) * ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k) / B ^ 2 := by
    have hscale : (∫ ω, ‖X ω‖ ^ 2 / B ^ 2 ∂μ) =
        (B ^ 2)⁻¹ * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
      rw [show (fun ω => ‖X ω‖ ^ 2 / B ^ 2) =
        (fun ω => (B ^ 2)⁻¹ * ‖X ω‖ ^ 2) by
          funext ω
          ring]
      rw [integral_const_mul]
    rw [hscale]
    calc
      (B ^ 2)⁻¹ * ∫ ω, ‖X ω‖ ^ 2 ∂μ ≤
          (B ^ 2)⁻¹ * ((2 * (mass⁻¹ ^ 2 * L ^ 3)) *
            ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k) :=
        mul_le_mul_of_nonneg_left hSecond (inv_nonneg.mpr (sq_nonneg B))
      _ = (2 * (mass⁻¹ ^ 2 * L ^ 3) *
          ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k) / B ^ 2 := by ring
  have hOfReal := ENNReal.ofReal_le_ofReal hIntegral
  change μ s ≤ _ at hMarkov
  rw [show μ = finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 3 N a mass ha hmass) by rfl] at hMarkov
  exact hMarkov.trans hOfReal

def periodic3DFiniteSourceGaussianMeasureH3 (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) : Measure Periodic3DCompletion :=
  Measure.map (periodic3DFiniteSourceFourierLiftH3 N a L)
    (finiteCovarianceGaussianMeasure
      (numberedLatticeCovarianceGJ 3 N a mass ha hmass))

instance periodic3DFiniteSourceGaussianMeasureH3_isProbability (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (periodic3DFiniteSourceGaussianMeasureH3 N a mass L ha hmass) := by
  unfold periodic3DFiniteSourceGaussianMeasureH3
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_periodic3DFiniteSourceFourierLiftH3 N a L).aemeasurable).2 inferInstance

theorem periodic3DFiniteSourceGaussianMeasureH3_apply (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (s : Set Periodic3DCompletion) (hs : MeasurableSet s) :
    periodic3DFiniteSourceGaussianMeasureH3 N a mass L ha hmass s =
      finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)
        ((periodic3DFiniteSourceFourierLiftH3 N a L) ⁻¹' s) := by
  rw [periodic3DFiniteSourceGaussianMeasureH3]
  exact Measure.map_apply
    (measurable_periodic3DFiniteSourceFourierLiftH3 N a L) hs

theorem periodic3DFiniteSourceFourierLiftH3_norm_eq_hminusTwo
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    ‖periodic3DFiniteSourceFourierLiftH2 N a L ω‖ =
      periodic3DHminusTwoNorm (periodic3DRawAtomicLift N a L hL ω) := by
  rw [← Real.sqrt_sq (norm_nonneg _), periodic3DFiniteSourceFourierLiftH2_norm_sq N a L ha hL]
  rfl

theorem periodic3DFiniteSourceFourierLiftH3_mem_two_ball
    (N : ℕ) [NeZero N] (a L B : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)))
    (hB : ‖periodic3DFiniteSourceFourierLiftH2 N a L ω‖ ≤ B) :
    periodic3DFiniteSourceFourierLiftH3 N a L ω ∈ periodic3DHminusTwoBallInHminusThree B := by
  refine ⟨periodic3DRawAtomicLift N a L hL ω,
    periodic3DRawAtomicLift_mem_carrier_two N a L ha hL ω, ?_, ?_⟩
  · calc
      periodic3DHminusTwoNorm (periodic3DRawAtomicLift N a L hL ω) =
          ‖periodic3DFiniteSourceFourierLiftH2 N a L ω‖ :=
        (periodic3DFiniteSourceFourierLiftH3_norm_eq_hminusTwo N a L ha hL ω).symm
      _ ≤ B := hB
  · apply lp.ext
    funext k
    have hraw := congrFun
      (periodic3DRawWeightedLift_eq_finiteSourceFourierLiftH3 N a L ha hL ω) k
    change periodic3DFiniteSourceFourierLiftH3 N a L ω k =
      (Real.sqrt (periodic3DSobolevWeight 3 k) : ℂ) *
        periodic3DRawAtomicLift N a L hL ω k
    exact hraw.symm

theorem periodic3DFiniteSourceGaussianMeasureH3_compactTail
    (N : ℕ) [NeZero N] (a mass L B : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) (hB : 0 < B) :
    periodic3DFiniteSourceGaussianMeasureH3 N a mass L ha hmass
      (closure (periodic3DHminusTwoBallInHminusThree B))ᶜ ≤
      ENNReal.ofReal ((2 * (mass⁻¹ ^ 2 * L ^ 3) *
        ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k) / B ^ 2) := by
  let μ := finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)
  let X := periodic3DFiniteSourceFourierLiftH2 N a L
  let Y := periodic3DFiniteSourceFourierLiftH3 N a L
  let K : Set Periodic3DCompletion := closure (periodic3DHminusTwoBallInHminusThree B)
  have hKcompact : IsCompact K := isCompact_closure_periodic3DHminusTwoBall B hB.le
  have hpre : Y ⁻¹' Kᶜ ⊆ {ω | B ^ 2 ≤ ‖X ω‖ ^ 2} := by
    intro ω hω
    by_contra htail
    have hnorm : ‖X ω‖ ≤ B := by
      have hh : ‖X ω‖ ^ 2 < B ^ 2 := lt_of_not_ge htail
      nlinarith [norm_nonneg (X ω)]
    exact hω (subset_closure
      (periodic3DFiniteSourceFourierLiftH3_mem_two_ball N a L B ha hL ω hnorm))
  rw [periodic3DFiniteSourceGaussianMeasureH3_apply N a mass L ha hmass Kᶜ
    hKcompact.isClosed.measurableSet.compl]
  exact (measure_mono hpre).trans
    (periodic3DFiniteSourceFourierLiftH2_markov_tail N a mass L B ha hmass hvol hL hB)

end Pphi2Clean.Continuum
