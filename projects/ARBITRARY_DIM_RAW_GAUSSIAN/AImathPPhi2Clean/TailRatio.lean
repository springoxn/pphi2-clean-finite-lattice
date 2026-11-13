import AImathPPhi2Clean.Periodic5DSobolevWeights
noncomputable section
namespace Pphi2Clean.DimensionFreeProbe

theorem target_fourier_term_le_radius_factor (k : Fin 122409 → ℤ) (R : ℕ)
    (hR : (R : ℝ) ≤ ‖k‖) :
    (1 + ‖k‖) ^ (-2 * (61206 : ℝ)) ≤
      (1 + (R : ℝ)) ^ (-2 : ℝ) * (1 + ‖k‖) ^ (-2 * (61205 : ℝ)) := by
  let x : ℝ := 1 + ‖k‖
  let y : ℝ := 1 + (R : ℝ)
  have hx : 0 < x := by dsimp [x]; exact add_pos_of_pos_of_nonneg one_pos (norm_nonneg k)
  have hy : 0 < y := by dsimp [y]; exact add_pos_of_pos_of_nonneg one_pos (Nat.cast_nonneg R)
  have hxy : y ≤ x := by
    change 1 + (R : ℝ) ≤ 1 + ‖k‖
    exact add_le_add_right hR 1
  have hdecay : x ^ (-2 : ℝ) ≤ y ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hy hxy (by norm_num)
  have hfactor : x ^ (-2 * (61206 : ℝ)) = x ^ (-2 : ℝ) * x ^ (-2 * (61205 : ℝ)) := by
    have he : -2 * (61206 : ℝ) = (-2 : ℝ) + (-2 * (61205 : ℝ)) := by norm_num
    rw [he, Real.rpow_add hx]
  change x ^ (-2 * (61206 : ℝ)) ≤ y ^ (-2 : ℝ) * x ^ (-2 * (61205 : ℝ))
  rw [hfactor]
  have henergy : 0 ≤ x ^ (-2 * (61205 : ℝ)) := Real.rpow_nonneg (le_of_lt hx) _
  exact mul_le_mul_of_nonneg_right hdecay henergy

#print axioms target_fourier_term_le_radius_factor
end Pphi2Clean.DimensionFreeProbe
