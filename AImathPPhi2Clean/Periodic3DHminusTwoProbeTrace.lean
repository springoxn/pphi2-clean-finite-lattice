import AImathPPhi2Clean.Periodic3DProbeMoment

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory

theorem periodic3DComplexFourierProbe_hminusTwo_weighted_trace_bound
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    Summable (fun k : Periodic3DIndex => periodic3DHminusTwoWeight k *
      periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k) ∧
    ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k *
      periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k ≤
      (2 * (mass⁻¹ ^ 2 * L ^ 3)) * ∑' k : Periodic3DIndex,
        periodic3DHminusTwoWeight k := by
  let C := 2 * (mass⁻¹ ^ 2 * L ^ 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hweight : Summable periodic3DHminusTwoWeight := periodic3DHminusTwoWeight_summable
  have hmajor : Summable (fun k : Periodic3DIndex => periodic3DHminusTwoWeight k * C) :=
    hweight.mul_right C
  have hnonneg : ∀ k : Periodic3DIndex, 0 ≤
      periodic3DHminusTwoWeight k *
        periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k := by
    intro k
    exact mul_nonneg (periodic3DSobolevWeight_nonneg 2 k)
      (periodic3DComplexFourierProbeMoment_nonneg N a mass L ha hmass hL k)
  have hle : ∀ k : Periodic3DIndex,
      periodic3DHminusTwoWeight k *
        periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k ≤
      periodic3DHminusTwoWeight k * C := by
    intro k
    dsimp [C, periodic3DHminusTwoWeight]
    exact mul_le_mul_of_nonneg_left
      (periodic3DComplexFourierProbeMoment_le N a mass L ha hmass hvol hL k)
      (periodic3DSobolevWeight_nonneg 2 k)
  constructor
  · exact hmajor.of_nonneg_of_le hnonneg hle
  · calc
      ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k *
          periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k ≤
          ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k * C :=
            ((hmajor.of_nonneg_of_le hnonneg hle).tsum_le_tsum hle hmajor)
      _ = C * ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k := by
            rw [tsum_mul_right]
            exact mul_comm _ _
      _ = _ := by ring

end Pphi2Clean.Continuum
