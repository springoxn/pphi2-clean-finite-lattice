import AImathPPhi2Clean.DimensionFreeWeightSummability
import AImathPPhi2Clean.TailRatio
noncomputable section
namespace Pphi2Clean.DimensionFreeProbe

def targetWeight (k : Fin 122409 → ℤ) : ℝ := (1 + ‖k‖) ^ (-2 * (61206 : ℝ))
def energyWeight (k : Fin 122409 → ℤ) : ℝ := (1 + ‖k‖) ^ (-2 * (61205 : ℝ))

theorem target_tail_sum_le (R : ℕ) :
    ∑' k : Fin 122409 → ℤ, (if (R : ℝ) < ‖k‖ then targetWeight k else 0) ≤
      (1 + (R : ℝ)) ^ (-2 : ℝ) * ∑' k : Fin 122409 → ℤ, energyWeight k := by
  have hTarget : Summable targetWeight := by
    change Summable (fun k : Fin 122409 → ℤ => (1 + ‖k‖) ^ (-2 * (61206 : ℝ)))
    exact target_weight_summable
  have hEnergy : Summable energyWeight := by
    change Summable (fun k : Fin 122409 → ℤ => (1 + ‖k‖) ^ (-2 * (61205 : ℝ)))
    exact energy_weight_summable
  have hTarget0 (k : Fin 122409 → ℤ) : 0 ≤ targetWeight k := by
    unfold targetWeight
    exact Real.rpow_nonneg (by linarith [norm_nonneg k]) _
  have hEnergy0 (k : Fin 122409 → ℤ) : 0 ≤ energyWeight k := by
    unfold energyWeight
    exact Real.rpow_nonneg (by linarith [norm_nonneg k]) _
  let tail : (Fin 122409 → ℤ) → ℝ := fun k =>
    if (R : ℝ) < ‖k‖ then targetWeight k else 0
  have hTail0 (k : Fin 122409 → ℤ) : 0 ≤ tail k := by
    by_cases h : (R : ℝ) < ‖k‖ <;> simp [tail, h, hTarget0]
  have hTail_le (k : Fin 122409 → ℤ) : tail k ≤ targetWeight k := by
    by_cases h : (R : ℝ) < ‖k‖
    · simp [tail, h]
    · simp [tail, h, hTarget0]
  have hTail : Summable tail := Summable.of_nonneg_of_le hTail0 hTail_le hTarget
  let factor : ℝ := (1 + (R : ℝ)) ^ (-2 : ℝ)
  have hFactor0 : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by exact add_nonneg (by norm_num) (Nat.cast_nonneg R)) _
  have hRightSummable : Summable (fun k => factor * energyWeight k) := hEnergy.mul_left factor
  have hPoint (k : Fin 122409 → ℤ) : tail k ≤ factor * energyWeight k := by
    by_cases h : (R : ℝ) < ‖k‖
    · have hcore := target_fourier_term_le_radius_factor k R (le_of_lt h)
      change (if (R : ℝ) < ‖k‖ then targetWeight k else 0) ≤ factor * energyWeight k
      rw [if_pos h]
      simpa [targetWeight, energyWeight, factor] using hcore
    · simp only [tail, if_neg h]
      exact mul_nonneg hFactor0 (hEnergy0 k)
  have hsum := Summable.tsum_le_tsum hPoint hTail hRightSummable
  simpa only [tsum_mul_left] using hsum

#print axioms target_tail_sum_le
end Pphi2Clean.DimensionFreeProbe
