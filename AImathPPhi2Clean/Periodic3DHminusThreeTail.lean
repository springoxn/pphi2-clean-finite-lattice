import AImathPPhi2Clean.Periodic3DCompactEmbedding

noncomputable section
namespace Pphi2Clean.Continuum

theorem periodic3D_hminusThree_to_hminusTwo_weight_ratio_tendsto_zero :
    ∀ δ : ℝ, 0 < δ → ∃ K : Finset Periodic3DIndex,
      ∀ k, k ∉ K → periodic3DSobolevWeight 3 k ≤ δ * periodic3DSobolevWeight 2 k := by
  intro δ hδ
  obtain ⟨K, hK⟩ := periodic3D_weight_ratio_tendsto_zero δ hδ
  refine ⟨K, ?_⟩
  intro k hk
  have h43 := hK k hk
  let b : ℝ := 1 + max ‖(fs4SplitIndex (periodic3DExtend k)).1‖
    ‖(fs4SplitIndex (periodic3DExtend k)).2‖
  have hb : 0 < b := by dsimp [b]; positivity
  have h2 : periodic3DSobolevWeight 2 k = b ^ (-(2 * (2 : ℝ))) := by
    simp [periodic3DSobolevWeight, fs4SobolevWeight, b]
  have h3 : periodic3DSobolevWeight 3 k = b ^ (-(2 * (3 : ℝ))) := by
    simp [periodic3DSobolevWeight, fs4SobolevWeight, b]
  have h4 : periodic3DSobolevWeight 4 k = b ^ (-(2 * (4 : ℝ))) := by
    simp [periodic3DSobolevWeight, fs4SobolevWeight, b]
  rw [h4, h3] at h43
  rw [h3, h2]
  have hexp : -(2 * (4 : ℝ)) = -(2 * (3 : ℝ)) + (-2 : ℝ) := by ring
  have hexp' : -(2 * (3 : ℝ)) = -(2 * (2 : ℝ)) + (-2 : ℝ) := by ring
  rw [hexp, Real.rpow_add hb] at h43
  have hsmall : b ^ (-2 : ℝ) ≤ δ := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hb (-(2 * (3 : ℝ))))).mp
    simpa [mul_comm, mul_left_comm, mul_assoc] using h43
  rw [hexp', Real.rpow_add hb]
  calc
    b ^ (-(2 * (2 : ℝ))) * b ^ (-2 : ℝ) ≤
        b ^ (-(2 * (2 : ℝ))) * δ :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos hb _).le
    _ = δ * b ^ (-(2 * (2 : ℝ))) := mul_comm _ _

end Pphi2Clean.Continuum
