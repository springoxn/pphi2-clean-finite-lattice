import AImathPPhi2Clean.Periodic3DHminusTwoEnergy
import AImathPPhi2Clean.Periodic3DHminusTwoRawCarrier

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

theorem periodic3DSiteSequence_mem_carrier_two (N : ℕ) [NeZero N]
    (a L : ℝ) (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DSiteSequence N a L j ∈ periodic3DCarrier 2 := by
  rw [periodic3DCarrier]
  have hmajor : Summable (fun k : Periodic3DIndex =>
      a ^ 6 * periodic3DHminusTwoWeight k) :=
    periodic3DHminusTwoWeight_summable.mul_left (a ^ 6)
  apply hmajor.of_nonneg_of_le
  · intro k
    exact mul_nonneg (periodic3DSobolevWeight_nonneg 2 k) (sq_nonneg _)
  · intro k
    have hnorm : ‖periodic3DSiteSequence N a L j k‖ ^ 2 = a ^ 6 := by
      dsimp [periodic3DSiteSequence]
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      calc
        (a ^ 3 * Real.cos (periodic3DSitePhase N a L j k)) ^ 2 +
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) ^ 2 =
            a ^ 6 * (Real.cos (periodic3DSitePhase N a L j k) ^ 2 +
              Real.sin (periodic3DSitePhase N a L j k) ^ 2) := by ring
        _ = a ^ 6 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    rw [hnorm]
    exact (mul_comm _ _).le

def periodic3DSiteWeightedSequenceH2 (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) : Periodic3DIndex → ℂ :=
  fun k => (Real.sqrt (periodic3DHminusTwoWeight k) : ℂ) *
    periodic3DSiteSequence N a L j k

theorem periodic3DSiteWeightedSequence_memLpH2 (N : ℕ) [NeZero N]
    (a L : ℝ) (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
    Memℓp (periodic3DSiteWeightedSequenceH2 N a L j) 2 :=
  periodic3D_weighted_coefficients_memLp2 2 (periodic3DSiteSequence N a L j)
    (periodic3DSiteSequence_mem_carrier_two N a L j)

def periodic3DSiteVectorH2 (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) : Periodic3DCompletion :=
  ⟨periodic3DSiteWeightedSequenceH2 N a L j,
    periodic3DSiteWeightedSequence_memLpH2 N a L j⟩

def periodic3DFiniteSourceCoefficientMapH2 (N : ℕ) [NeZero N]
    (a L : ℝ) (c : Fin (Fintype.card (FinLatticeSites 3 N)) → ℝ) :
    Periodic3DCompletion :=
  ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
    c j • periodic3DSiteVectorH2 N a L j

theorem continuous_periodic3DFiniteSourceCoefficientMapH2 (N : ℕ) [NeZero N]
    (a L : ℝ) : Continuous (periodic3DFiniteSourceCoefficientMapH2 N a L) := by
  unfold periodic3DFiniteSourceCoefficientMapH2
  exact continuous_finsetSum Finset.univ (fun j _ =>
    (continuous_apply j).smul continuous_const)

def periodic3DFiniteSourceFourierLiftH2 (N : ℕ) [NeZero N]
    (a L : ℝ)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    Periodic3DCompletion :=
  periodic3DFiniteSourceCoefficientMapH2 N a L
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N))) )

theorem measurable_periodic3DFiniteSourceFourierLiftH2 (N : ℕ) [NeZero N]
    (a L : ℝ) : Measurable (periodic3DFiniteSourceFourierLiftH2 N a L) := by
  unfold periodic3DFiniteSourceFourierLiftH2
  have hcoords : Measurable (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 3 N)) =>
        fun j : Fin (Fintype.card (FinLatticeSites 3 N)) =>
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N)))) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N)))).comp (comap_measurable _)
  exact (continuous_periodic3DFiniteSourceCoefficientMapH2 N a L).measurable.comp hcoords

theorem periodic3DFiniteSourceFourierLift_applyH2 (N : ℕ) [NeZero N]
    (a L : ℝ)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)))
    (k : Periodic3DIndex) :
    periodic3DFiniteSourceFourierLiftH2 N a L ω k =
      ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
          periodic3DSiteWeightedSequenceH2 N a L j k := by
  change (⇑(periodic3DFiniteSourceCoefficientMapH2 N a L
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N))))) ) k = _
  rw [periodic3DFiniteSourceCoefficientMapH2, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    periodic3DSiteVectorH2, Complex.real_smul]

theorem periodic3DRawWeightedLift_eq_finiteSourceFourierLiftH2 (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    (fun k => (Real.sqrt (periodic3DHminusTwoWeight k) : ℂ) *
        periodic3DRawAtomicLift N a L hL ω k) =
      fun k => periodic3DFiniteSourceFourierLiftH2 N a L ω k := by
  funext k
  rw [periodic3DRawAtomicLift_eq_site_sumH3 N a L ha hL ω]
  rw [periodic3DFiniteSourceFourierLift_applyH2]
  simp only [periodic3DSiteWeightedSequenceH2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem periodic3DFiniteSourceFourierLiftH2_norm_sq (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    ‖periodic3DFiniteSourceFourierLiftH2 N a L ω‖ ^ 2 =
      ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k *
        ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
    (periodic3DFiniteSourceFourierLiftH2 N a L ω)
  norm_num at hnorm
  rw [hnorm]
  apply tsum_congr
  intro k
  have hraw := congrFun
    (periodic3DRawWeightedLift_eq_finiteSourceFourierLiftH2 N a L ha hL ω) k
  rw [← hraw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  change (Real.sqrt (periodic3DSobolevWeight 2 k)) ^ 2 *
      ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2 =
      periodic3DSobolevWeight 2 k * ‖periodic3DRawAtomicLift N a L hL ω k‖ ^ 2
  rw [Real.sq_sqrt (periodic3DSobolevWeight_nonneg 2 k)]

set_option maxHeartbeats 1000000 in
theorem periodic3DFiniteSourceFourierLiftH2_integrable_norm_sq
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
      ‖periodic3DFiniteSourceFourierLiftH2 N a L ω‖ ^ 2)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) := by
  let T := numberedLatticeCovarianceGJ 3 N a mass ha hmass
  let μ := finiteCovarianceGaussianMeasure T
  have hcoord (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
      MemLp (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
        ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N)))) 2 μ := by
    have hg := finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T
      (Pi.single j (1 : ℝ))
    exact hg.memLp_two
  have hsum : MemLp (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 3 N)) =>
      ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℝ) •
          periodic3DSiteVectorH2 N a L j) 2 μ := by
    have hsum' : MemLp (∑ j ∈ (Finset.univ : Finset
        (Fin (Fintype.card (FinLatticeSites 3 N)))),
        fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) =>
          (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) : ℝ) •
            periodic3DSiteVectorH2 N a L j) 2 μ := by
      apply MeasureTheory.memLp_finsetSum'
      intro j hj
      have hconst : MemLp (fun _ : FiniteLatticeConfiguration
          (Fintype.card (FinLatticeSites 3 N)) =>
            periodic3DSiteVectorH2 N a L j) ⊤ μ := memLp_const _
      exact hconst.smul (hcoord j)
    convert hsum' using 1
    ext ω
    simp [Finset.sum_apply]
  change Integrable (fun ω : FiniteLatticeConfiguration
    (Fintype.card (FinLatticeSites 3 N)) =>
      ‖periodic3DFiniteSourceFourierLiftH2 N a L ω‖ ^ 2) μ
  have hmap : MemLp (periodic3DFiniteSourceFourierLiftH2 N a L) 2 μ := by
    change MemLp (fun ω => periodic3DFiniteSourceCoefficientMapH2 N a L
      (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
        (Fintype.card (FinLatticeSites 3 N)))) ) 2 μ
    unfold periodic3DFiniteSourceCoefficientMapH2
    convert hsum using 1
  exact hmap.integrable_norm_pow'

theorem periodic3DFiniteSourceFourierLiftH2_integral_norm_sq_le
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hvol : a * (N : ℝ) = L) (hL : 0 < L) :
    (∫ ω, ‖periodic3DFiniteSourceFourierLiftH2 N a L ω‖ ^ 2
      ∂finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 3 N a mass ha hmass)) ≤
      2 * (mass⁻¹ ^ 2 * L ^ 3) * ∑' k : Periodic3DIndex, periodic3DHminusTwoWeight k := by
  simp_rw [periodic3DFiniteSourceFourierLiftH2_norm_sq N a L ha hL]
  exact periodic3DRawAtomicLift_integral_energy_hminusTwo_le N a mass L ha hmass hvol hL

end Pphi2Clean.Continuum
