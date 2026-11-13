import AImathPPhi2Clean.Periodic3DHminusThreeTailBound
import AImathPPhi2Clean.Periodic3DHminusThreeWeightMonotonicity
import AImathPPhi2Clean.Periodic3DWeightedCarrier

noncomputable section
namespace Pphi2Clean.Continuum

abbrev periodic3DHminusTwoCoefficientCarrier := periodic3DCarrier 2
abbrev periodic3DHminusThreeCoefficientCarrier' := periodic3DCarrier 3

def periodic3DHminusTwoNorm (c : Periodic3DIndex → ℂ) : ℝ :=
  Real.sqrt (∑' k, periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2)

theorem periodic3D_hminusTwo_coefficients_in_hminusThree (c : Periodic3DIndex → ℂ)
    (hc : c ∈ periodic3DHminusTwoCoefficientCarrier) :
    c ∈ periodic3DHminusThreeCoefficientCarrier' := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (periodic3DSobolevWeight_nonneg 3 k) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right
      (periodic3DHminusThreeWeight_le_hminusTwo k) (sq_nonneg _)) hc

theorem periodic3DHminusThreeEmbedding_norm_le_hminusTwo (c : Periodic3DIndex → ℂ)
    (hc : c ∈ periodic3DHminusTwoCoefficientCarrier) :
    ‖periodic3DEmbeddingOfCoefficients 3 c
      (periodic3D_hminusTwo_coefficients_in_hminusThree c hc)‖ ≤
        periodic3DHminusTwoNorm c := by
  rw [periodic3DHminusThreeEmbedding_norm_eq]
  unfold periodic3DHminusThreeNorm periodic3DHminusTwoNorm
  apply Real.sqrt_le_sqrt
  have hc3 := periodic3D_hminusTwo_coefficients_in_hminusThree c hc
  exact hc3.tsum_le_tsum (fun k =>
    mul_le_mul_of_nonneg_right (periodic3DHminusThreeWeight_le_hminusTwo k)
      (sq_nonneg (‖c k‖))) hc

theorem periodic3DHminusTwo_uniform_hminusThree_tail :
    ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
      ∃ K : Finset Periodic3DIndex, ∀ c : Periodic3DIndex → ℂ,
        c ∈ periodic3DHminusTwoCoefficientCarrier →
        periodic3DHminusTwoNorm c ≤ R →
        Real.sqrt (∑' k, if k ∉ K then
          periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 else 0) < ε := by
  intro R hR ε hε
  let δ := (ε / (R + 1)) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK⟩ := periodic3D_hminusThree_to_hminusTwo_weight_ratio_tendsto_zero δ hδ
  refine ⟨K, ?_⟩
  intro c hc hnorm
  have hnorm_sq : (∑' k : Periodic3DIndex,
      periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2) ≤ R ^ 2 := by
    change Real.sqrt (∑' k : Periodic3DIndex,
      periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2) ≤ R at hnorm
    exact (Real.sqrt_le_iff).mp hnorm |>.2
  have htail := periodic3D_hminusThree_tail_sq_le_of_weight_ratio K δ hδ.le hK hc
  have htail_nonneg : 0 ≤ ∑' k : Periodic3DIndex, if k ∉ K then
      periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 else 0 :=
    tsum_nonneg fun k => by
      by_cases hk : k ∉ K
      · simp [hk]
        exact mul_nonneg (periodic3DSobolevWeight_nonneg 3 k) (sq_nonneg ‖c k‖)
      · simp [hk]
  apply (Real.sqrt_lt htail_nonneg hε.le).2
  calc
    (∑' k : Periodic3DIndex, if k ∉ K then
        periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 else 0) ≤
        δ * (∑' k : Periodic3DIndex,
          periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2) := htail
    _ ≤ δ * R ^ 2 := mul_le_mul_of_nonneg_left hnorm_sq hδ.le
    _ < ε ^ 2 := by
      dsimp [δ]
      have hden : 0 < R + 1 := by linarith
      have hratio_nonneg : 0 ≤ R / (R + 1) := div_nonneg hR hden.le
      have hratio_lt : R / (R + 1) < 1 := (div_lt_one hden).2 (by linarith)
      have hratio_sq : (R / (R + 1)) ^ 2 < 1 := by
        have hsum_pos : 0 < 1 + R / (R + 1) := by linarith
        nlinarith [mul_pos (sub_pos.mpr hratio_lt) hsum_pos]
      have hcalc : (ε / (R + 1)) ^ 2 * R ^ 2 =
          ε ^ 2 * (R / (R + 1)) ^ 2 := by
        field_simp [ne_of_gt hden] <;> ring
      rw [hcalc]
      calc
        ε ^ 2 * (R / (R + 1)) ^ 2 < ε ^ 2 * 1 :=
          mul_lt_mul_of_pos_left hratio_sq (sq_pos_of_pos hε)
        _ = ε ^ 2 := by ring

end Pphi2Clean.Continuum
