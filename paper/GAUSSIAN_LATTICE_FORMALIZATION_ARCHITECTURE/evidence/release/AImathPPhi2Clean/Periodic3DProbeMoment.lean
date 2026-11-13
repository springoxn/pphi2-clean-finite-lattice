import AImathPPhi2Clean.Periodic3DFiniteSourceLift
import AImathPPhi2Clean.Periodic3DWeightedCarrier
import AImathPPhi2Clean.RealFourierSecondMoment

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

def periodic3DComplexFourierProbe (L : ℝ) (hL : 0 < L)
    (k : Periodic3DIndex)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 3 → ℝ) ℝ)) : ℂ :=
  (ω (periodicCosineTest 3 L k hL) : ℂ) +
    (ω (periodicSineTest 3 L k hL) : ℂ) * Complex.I

theorem periodic3DComplexFourierProbe_norm_sq (L : ℝ) (hL : 0 < L)
    (k : Periodic3DIndex)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 3 → ℝ) ℝ)) :
    ‖periodic3DComplexFourierProbe L hL k ω‖ ^ 2 =
      (ω (periodicCosineTest 3 L k hL)) ^ 2 +
        (ω (periodicSineTest 3 L k hL)) ^ 2 := by
  unfold periodic3DComplexFourierProbe
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

def periodic3DComplexFourierProbeMoment (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) (k : Periodic3DIndex) : ℝ :=
  ∫ ω, ‖periodic3DComplexFourierProbe L hL k ω‖ ^ 2 ∂
    physicalGJMeasure 3 N a mass ha hmass

theorem periodic3DComplexFourierProbeMoment_le (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) (k : Periodic3DIndex) :
    periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k ≤
      2 * (mass⁻¹ ^ 2 * L ^ 3) := by
  unfold periodic3DComplexFourierProbeMoment
  have hcosLaw := physicalGJMeasure_eval_hasGaussianLaw 3 N a mass ha hmass
    (periodicCosineTest 3 L k hL)
  have hsinLaw := physicalGJMeasure_eval_hasGaussianLaw 3 N a mass ha hmass
    (periodicSineTest 3 L k hL)
  have hcosInt : Integrable (fun ω => (ω (periodicCosineTest 3 L k hL)) ^ 2)
      (physicalGJMeasure 3 N a mass ha hmass) := hcosLaw.memLp_two.integrable_sq
  have hsinInt : Integrable (fun ω => (ω (periodicSineTest 3 L k hL)) ^ 2)
      (physicalGJMeasure 3 N a mass ha hmass) := hsinLaw.memLp_two.integrable_sq
  have hcos := physicalGJMeasure_periodicCosineTest_second_moment_le
    3 N a mass L ha hmass hvol k hL
  have hsin := physicalGJMeasure_periodicSineTest_second_moment_le
    3 N a mass L ha hmass hvol k hL
  calc
    (∫ ω, ‖periodic3DComplexFourierProbe L hL k ω‖ ^ 2
        ∂physicalGJMeasure 3 N a mass ha hmass) =
      ∫ ω, (ω (periodicCosineTest 3 L k hL)) ^ 2 +
        (ω (periodicSineTest 3 L k hL)) ^ 2
        ∂physicalGJMeasure 3 N a mass ha hmass := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact periodic3DComplexFourierProbe_norm_sq L hL k ω
    _ = (∫ ω, (ω (periodicCosineTest 3 L k hL)) ^ 2
          ∂physicalGJMeasure 3 N a mass ha hmass) +
        ∫ ω, (ω (periodicSineTest 3 L k hL)) ^ 2
          ∂physicalGJMeasure 3 N a mass ha hmass := integral_add hcosInt hsinInt
    _ ≤ mass⁻¹ ^ 2 * L ^ 3 + mass⁻¹ ^ 2 * L ^ 3 := add_le_add hcos hsin
    _ = 2 * (mass⁻¹ ^ 2 * L ^ 3) := by ring

theorem periodic3DComplexFourierProbeMoment_nonneg (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) (k : Periodic3DIndex) :
    0 ≤ periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k := by
  unfold periodic3DComplexFourierProbeMoment
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem periodic3DComplexFourierProbe_weighted_trace_bound (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    Summable (fun k : Periodic3DIndex => periodic3DHminusThreeWeight k *
      periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k) ∧
    ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k *
      periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k ≤
      (2 * (mass⁻¹ ^ 2 * L ^ 3)) * ∑' k : Periodic3DIndex,
        periodic3DHminusThreeWeight k := by
  let C := 2 * (mass⁻¹ ^ 2 * L ^ 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hweight : Summable periodic3DHminusThreeWeight := periodic3DHminusThreeWeight_summable
  have hmajor : Summable (fun k : Periodic3DIndex => periodic3DHminusThreeWeight k * C) :=
    hweight.mul_right C
  have hnonneg : ∀ k : Periodic3DIndex, 0 ≤
      periodic3DHminusThreeWeight k *
        periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k := by
    intro k
    exact mul_nonneg (periodic3DHminusThreeWeight_nonneg k)
      (periodic3DComplexFourierProbeMoment_nonneg N a mass L ha hmass hL k)
  have hle : ∀ k : Periodic3DIndex,
      periodic3DHminusThreeWeight k *
        periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k ≤
      periodic3DHminusThreeWeight k * C := by
    intro k
    dsimp [C]
    exact mul_le_mul_of_nonneg_left
      (periodic3DComplexFourierProbeMoment_le N a mass L ha hmass hvol hL k)
      (periodic3DHminusThreeWeight_nonneg k)
  constructor
  · exact hmajor.of_nonneg_of_le hnonneg hle
  · calc
      ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k *
          periodic3DComplexFourierProbeMoment N a mass L ha hmass hL k ≤
          ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k * C :=
            (hmajor.of_nonneg_of_le hnonneg hle).tsum_le_tsum hle hmajor
      _ = C * ∑' k : Periodic3DIndex, periodic3DHminusThreeWeight k := by
            rw [tsum_mul_right]
            exact mul_comm _ _
      _ = _ := by ring

end Pphi2Clean.Continuum
