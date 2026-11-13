import AImathPPhi2Clean.PeriodicFS4DRealCarrier
import AImathPPhi2Clean.Periodic3DSobolevWeights

noncomputable section

namespace Pphi2Clean.Continuum

abbrev Periodic3DCompletion := lp (fun _ : Periodic3DIndex => ℂ) 2

def periodic3DWeightedFourierCoefficients (s : ℝ)
    (c : Periodic3DIndex → ℂ) : Periodic3DIndex → ℂ :=
  fun k => (Real.sqrt (periodic3DSobolevWeight s k) : ℂ) * c k

def periodic3DCarrier (s : ℝ) : Set (Periodic3DIndex → ℂ) :=
  {c | Summable (fun k => periodic3DSobolevWeight s k * ‖c k‖ ^ 2)}

theorem periodic3DHminusThreeWeight_nonneg (k : Periodic3DIndex) :
    0 ≤ periodic3DHminusThreeWeight k :=
  periodic3DSobolevWeight_nonneg 3 k

theorem periodic3DHminusFourWeight_nonneg (k : Periodic3DIndex) :
    0 ≤ periodic3DHminusFourWeight k :=
  periodic3DSobolevWeight_nonneg 4 k

theorem periodic3D_weighted_coefficients_memLp2 (s : ℝ)
    (c : Periodic3DIndex → ℂ)
    (hc : c ∈ periodic3DCarrier s) : Memℓp (periodic3DWeightedFourierCoefficients s c) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  change Summable (fun k => ‖(Real.sqrt (periodic3DSobolevWeight s k) : ℂ) * c k‖ ^ (2 : ℝ))
  change Summable (fun k => periodic3DSobolevWeight s k * ‖c k‖ ^ 2) at hc
  apply hc.congr
  intro k
  have hw := periodic3DSobolevWeight_nonneg s k
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt hw]

def periodic3DEmbeddingOfCoefficients (s : ℝ) (c : Periodic3DIndex → ℂ)
    (hc : c ∈ periodic3DCarrier s) : Periodic3DCompletion :=
  ⟨periodic3DWeightedFourierCoefficients s c,
    periodic3D_weighted_coefficients_memLp2 s c hc⟩

def periodic3DHminusThreeNorm (c : Periodic3DIndex → ℂ) : ℝ :=
  Real.sqrt (∑' k, periodic3DHminusThreeWeight k * ‖c k‖ ^ 2)

def periodic3DHminusFourNorm (c : Periodic3DIndex → ℂ) : ℝ :=
  Real.sqrt (∑' k, periodic3DHminusFourWeight k * ‖c k‖ ^ 2)

theorem periodic3DHminusThreeEmbedding_norm_eq (c : Periodic3DIndex → ℂ)
    (hc : c ∈ periodic3DCarrier 3) :
    ‖periodic3DEmbeddingOfCoefficients 3 c hc‖ = periodic3DHminusThreeNorm c := by
  unfold periodic3DHminusThreeNorm
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply tsum_congr
  intro k
  simp only [periodic3DEmbeddingOfCoefficients, periodic3DWeightedFourierCoefficients, periodic3DHminusThreeWeight]
  have hw := periodic3DSobolevWeight_nonneg 3 k
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt hw]

theorem periodic3DHminusFourEmbedding_norm_le_hminusThreeNorm
    (c : Periodic3DIndex → ℂ) (hc : c ∈ periodic3DCarrier 3) :
    ‖periodic3DEmbeddingOfCoefficients 4 c
      (by
        change Summable (fun k => periodic3DHminusFourWeight k * ‖c k‖ ^ 2)
        change Summable (fun k => periodic3DHminusThreeWeight k * ‖c k‖ ^ 2) at hc
        apply Summable.of_nonneg_of_le
          (fun k => mul_nonneg (periodic3DHminusFourWeight_nonneg k) (sq_nonneg _))
          (fun k => mul_le_mul_of_nonneg_right (periodic3DHminusFourWeight_le_three k) (sq_nonneg _)) hc)‖ ≤
      periodic3DHminusThreeNorm c := by
  let hc4 : c ∈ periodic3DCarrier 4 := by
    change Summable (fun k => periodic3DHminusFourWeight k * ‖c k‖ ^ 2)
    change Summable (fun k => periodic3DHminusThreeWeight k * ‖c k‖ ^ 2) at hc
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (periodic3DHminusFourWeight_nonneg k) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right (periodic3DHminusFourWeight_le_three k) (sq_nonneg _)) hc
  have hsum4 : Summable (fun k => periodic3DHminusFourWeight k * ‖c k‖ ^ 2) := hc4
  have hsum3 : Summable (fun k => periodic3DHminusThreeWeight k * ‖c k‖ ^ 2) := hc
  have hnn4 : ∀ k, 0 ≤ periodic3DHminusFourWeight k * ‖c k‖ ^ 2 :=
    fun k => mul_nonneg (periodic3DHminusFourWeight_nonneg k) (sq_nonneg _)
  have hnn3 : ∀ k, 0 ≤ periodic3DHminusThreeWeight k * ‖c k‖ ^ 2 :=
    fun k => mul_nonneg (periodic3DHminusThreeWeight_nonneg k) (sq_nonneg _)
  have hle : ∀ k, periodic3DHminusFourWeight k * ‖c k‖ ^ 2 ≤ periodic3DHminusThreeWeight k * ‖c k‖ ^ 2 :=
    fun k => mul_le_mul_of_nonneg_right (periodic3DHminusFourWeight_le_three k) (sq_nonneg _)
  have hE : (∑' k, ENNReal.ofReal (periodic3DHminusFourWeight k * ‖c k‖ ^ 2)) ≤
      ∑' k, ENNReal.ofReal (periodic3DHminusThreeWeight k * ‖c k‖ ^ 2) :=
    ENNReal.tsum_le_tsum (fun k => ENNReal.ofReal_le_ofReal (hle k))
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn4 hsum4,
    ← ENNReal.ofReal_tsum_of_nonneg hnn3 hsum3] at hE
  have hreal : (∑' k, periodic3DHminusFourWeight k * ‖c k‖ ^ 2) ≤
      ∑' k, periodic3DHminusThreeWeight k * ‖c k‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hnn3)).mp hE
  have hnorm4 : ‖periodic3DEmbeddingOfCoefficients 4 c hc4‖ = periodic3DHminusFourNorm c := by
    unfold periodic3DHminusFourNorm
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
    rw [Real.sqrt_eq_rpow]
    congr 1
    apply tsum_congr
    intro k
    simp only [periodic3DEmbeddingOfCoefficients, periodic3DWeightedFourierCoefficients, periodic3DHminusFourWeight]
    have hw := periodic3DSobolevWeight_nonneg 4 k
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt hw]
  rw [hnorm4]
  unfold periodic3DHminusFourNorm periodic3DHminusThreeNorm
  exact Real.sqrt_le_sqrt hreal

end Pphi2Clean.Continuum
