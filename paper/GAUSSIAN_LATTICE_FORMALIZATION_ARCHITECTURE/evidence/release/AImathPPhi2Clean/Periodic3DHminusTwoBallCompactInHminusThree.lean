import AImathPPhi2Clean.Periodic3DHminusTwoToHminusThree
import AImathPPhi2Clean.Periodic3DCompactEmbedding

noncomputable section
namespace Pphi2Clean.Continuum

abbrev Periodic3DHminusThreeCompletion := Periodic3DCompletion

def periodic3DHminusTwoBallInHminusThree (B : ℝ) : Set Periodic3DHminusThreeCompletion :=
  {x | ∃ c : Periodic3DIndex → ℂ, ∃ hc : c ∈ periodic3DHminusTwoCoefficientCarrier,
    periodic3DHminusTwoNorm c ≤ B ∧
      x = periodic3DEmbeddingOfCoefficients 3 c
        (periodic3D_hminusTwo_coefficients_in_hminusThree c hc)}

theorem periodic3DHminusTwoBall_compact_approximation (B : ℝ) (hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Set Periodic3DHminusThreeCompletion, IsCompact T ∧
      ∀ x ∈ periodic3DHminusTwoBallInHminusThree B, ∃ y ∈ T, dist x y < ε := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ := periodic3DHminusTwo_uniform_hminusThree_tail B hB η hη
  let T := periodic3DHminusFourFiniteProjection K ''
    {z : {k // k ∈ K} → ℂ | ∀ k, ‖z k‖ ≤ B}
  have hT : IsCompact T := periodic3DHminusFourFiniteProjection_boundedBall_compact K B
  refine ⟨T, hT, ?_⟩
  intro x hx
  rcases hx with ⟨c, hc, hcB, rfl⟩
  let hc3 := periodic3D_hminusTwo_coefficients_in_hminusThree c hc
  let xh := periodic3DEmbeddingOfCoefficients 3 c hc3
  let z : {k // k ∈ K} → ℂ := fun k => xh (k : Periodic3DIndex)
  have hz : ∀ k, ‖z k‖ ≤ B := by
    intro k
    calc
      ‖z k‖ ≤ ‖xh‖ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) xh _
      _ ≤ periodic3DHminusTwoNorm c := periodic3DHminusThreeEmbedding_norm_le_hminusTwo c hc
      _ ≤ B := hcB
  let y := periodic3DHminusFourFiniteProjection K z
  refine ⟨y, ⟨z, hz, rfl⟩, ?_⟩
  have htail := hK c hc hcB
  let q : ℝ := ∑' k : Periodic3DIndex, if k ∉ K then
    periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2 else 0
  have hq : 0 ≤ q := by
    dsimp [q]
    apply tsum_nonneg
    intro k
    by_cases hk : k ∉ K
    · simp [hk]
      exact mul_nonneg (periodic3DSobolevWeight_nonneg 3 k) (sq_nonneg _)
    · simp [hk]
  have hqη : Real.sqrt q < η := by
    dsimp [q] at htail ⊢
    exact htail
  have herror_sq : ‖xh - y‖ ^ (2 : ℝ) = q := by
    rw [periodic3D_lp_fourier_projection_error_sq_eq_tail]
    dsimp [y, z, xh, q]
    apply tsum_congr
    intro k
    by_cases hk : k ∉ K
    · simp only [hk]
      change ‖periodic3DWeightedFourierCoefficients 3 c k‖ ^ 2 =
        periodic3DSobolevWeight 3 k * ‖c k‖ ^ 2
      have hw := periodic3DSobolevWeight_nonneg 3 k
      simp [periodic3DWeightedFourierCoefficients, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Real.sq_sqrt hw]
    · simp [hk]
  have hnorm_eq : ‖xh - y‖ = Real.sqrt q := by
    calc
      ‖xh - y‖ = Real.sqrt (‖xh - y‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt q := by
        congr 1
        exact_mod_cast herror_sq
  dsimp [η] at hqη
  calc
    dist xh y = ‖xh - y‖ := dist_eq_norm xh y
    _ = Real.sqrt q := hnorm_eq
    _ < ε / 2 := hqη
    _ < ε := by linarith

theorem periodic3DHminusTwoBall_totallyBounded (B : ℝ) (hB : 0 ≤ B) :
    TotallyBounded (periodic3DHminusTwoBallInHminusThree B) :=
  periodic3D_totallyBounded_of_compact_approximation
    (periodic3DHminusTwoBall_compact_approximation B hB)

theorem isCompact_closure_periodic3DHminusTwoBall (B : ℝ) (hB : 0 ≤ B) :
    IsCompact (closure (periodic3DHminusTwoBallInHminusThree B)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨(periodic3DHminusTwoBall_totallyBounded B hB).closure,
    isClosed_closure.isComplete⟩

end Pphi2Clean.Continuum
