import AImathPPhi2Clean.Periodic3DHminusThreeTail

noncomputable section
namespace Pphi2Clean.Continuum

theorem periodic3D_hminusThree_tail_sq_le_of_weight_ratio
    {c : Periodic3DIndex → ℂ} (K : Finset Periodic3DIndex) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hweight : ∀ k, k ∉ K → periodic3DSobolevWeight 3 k ≤ δ * periodic3DSobolevWeight 2 k)
    (hc : Summable (fun k : Periodic3DIndex => periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2)) :
    (∑' k, if k ∉ K then periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 else 0) ≤
      δ * (∑' k, periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2) := by
  have hmajor : Summable (fun k : Periodic3DIndex =>
      δ * (periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2)) := by
    simpa only [mul_assoc] using hc.mul_left δ
  have htail : Summable (fun k : Periodic3DIndex => if k ∉ K then
      periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 else 0) := by
    refine Summable.of_nonneg_of_le
      (f := fun k : Periodic3DIndex => δ *
        (periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2))
      (g := fun k : Periodic3DIndex => if k ∉ K then
        periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 else 0) ?_ ?_ hmajor
    · intro k
      by_cases hk : k ∈ K
      · simp [hk]
      · simp [hk]
        exact mul_nonneg (periodic3DSobolevWeight_nonneg 3 k) (sq_nonneg _)
    · intro k
      by_cases hk : k ∈ K
      · simp [hk]
        exact mul_nonneg hδ (mul_nonneg (periodic3DSobolevWeight_nonneg 2 k) (sq_nonneg _))
      · simp [hk]
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_right (hweight k hk) (sq_nonneg (‖c k‖)))
  calc
    (∑' k : Periodic3DIndex, if k ∉ K then
        periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 else 0) ≤
        ∑' k, δ * (periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2) := by
      exact htail.tsum_le_tsum (fun k => by
        by_cases hk : k ∈ K
        · simp [hk]
          exact mul_nonneg hδ (mul_nonneg (periodic3DSobolevWeight_nonneg 2 k) (sq_nonneg _))
        · simp [hk]
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_right (hweight k hk) (sq_nonneg (‖c k‖)))) hmajor
    _ = δ * (∑' k, periodic3DSobolevWeight 2 k * ‖c k‖ ^ 2) := by
      rw [tsum_mul_left]

end Pphi2Clean.Continuum
