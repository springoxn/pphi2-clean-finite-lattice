import AImathPPhi2Clean.Periodic3DHminusThreeFixedVolumeTightness
import AImathPPhi2Clean.Periodic3DGaussianWeakLimit

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology Pphi2Clean.UpstreamLattice

/-- The continuous inclusion of H⁻³ into H⁻⁴ in weighted coordinates. -/
def periodic3DH3ToH4Factor (k : Periodic3DIndex) : ℝ :=
  Real.sqrt (periodic3DSobolevWeight 4 k) / Real.sqrt (periodic3DSobolevWeight 3 k)

theorem periodic3DH3ToH4Factor_pos (k : Periodic3DIndex) :
    0 < periodic3DH3ToH4Factor k := by
  exact div_pos (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 4 _))
    (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 3 _))

theorem periodic3DH3ToH4Factor_le_one (k : Periodic3DIndex) :
    periodic3DH3ToH4Factor k ≤ 1 := by
  apply (div_le_one (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 3 _))).2
  exact Real.sqrt_le_sqrt (periodic3DHminusFourWeight_le_three k)

def periodic3DH3ToH4 (x : Periodic3DCompletion) : Periodic3DCompletion :=
  ⟨fun k => (periodic3DH3ToH4Factor k : ℂ) * x k, by
    change Memℓp (fun k => (periodic3DH3ToH4Factor k : ℂ) * x k) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
    have hx := (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)
    norm_num at hx ⊢
    apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _ hx
    intro k
    rw [abs_of_pos (periodic3DH3ToH4Factor_pos k)]
    exact (sq_le_sq₀ (mul_nonneg (periodic3DH3ToH4Factor_pos k).le (norm_nonneg _)) (norm_nonneg _)).2
      (mul_le_of_le_one_left (norm_nonneg _) (periodic3DH3ToH4Factor_le_one k))⟩

theorem periodic3DH3ToH4_norm_le (x : Periodic3DCompletion) :
    ‖periodic3DH3ToH4 x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hx := lp.norm_rpow_eq_tsum hp x
  have hy := lp.norm_rpow_eq_tsum hp (periodic3DH3ToH4 x)
  norm_num at hx hy
  rw [hx, hy]
  apply Summable.tsum_le_tsum
  · intro k
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    change ‖(periodic3DH3ToH4Factor k : ℂ) * x k‖ ≤ ‖x k‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (periodic3DH3ToH4Factor_pos k)]
    exact mul_le_of_le_one_left (norm_nonneg _) (periodic3DH3ToH4Factor_le_one k)
  · simpa using (lp.memℓp (periodic3DH3ToH4 x)).summable hp
  · simpa using (lp.memℓp x).summable hp

def periodic3DH3ToH4CLM : Periodic3DCompletion →L[ℝ] Periodic3DCompletion :=
  LinearMap.mkContinuous
    { toFun := periodic3DH3ToH4
      map_add' := by intro x y; apply lp.ext; funext k; change (periodic3DH3ToH4Factor k : ℂ) * (x k + y k) = (periodic3DH3ToH4Factor k : ℂ) * x k + (periodic3DH3ToH4Factor k : ℂ) * y k; ring
      map_smul' := by intro r x; apply lp.ext; funext k; simp [periodic3DH3ToH4, Complex.real_smul]; ring }
    1 (by intro x; simpa using periodic3DH3ToH4_norm_le x)

theorem periodic3DH3ToH4_injective : Function.Injective periodic3DH3ToH4 := by
  intro x y h
  apply lp.ext
  funext k
  have hk := congrArg (fun z : Periodic3DCompletion => z k) h
  change (periodic3DH3ToH4Factor k : ℂ) * x k =
    (periodic3DH3ToH4Factor k : ℂ) * y k at hk
  exact mul_left_cancel₀ (by exact_mod_cast (periodic3DH3ToH4Factor_pos k).ne') hk

theorem periodic3DH3ToH4_finiteSource (N : ℕ) [NeZero N]
    (a L : ℝ) (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DH3ToH4 (periodic3DFiniteSourceFourierLiftH3 N a L ω) =
      periodic3DFiniteSourceFourierLift N a L ω := by
  apply lp.ext
  funext k
  change (periodic3DH3ToH4Factor k : ℂ) *
    periodic3DFiniteSourceFourierLiftH3 N a L ω k = _
  rw [periodic3DFiniteSourceFourierLift_applyH3, periodic3DFiniteSourceFourierLift_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [periodic3DSiteWeightedSequenceH3, periodic3DSiteWeightedSequence,
    periodic3DH3ToH4Factor, Complex.ofReal_div]
  have hroot : (Real.sqrt (periodic3DHminusThreeWeight k) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 3 (periodic3DExtend k))).ne'
  change ((Real.sqrt (periodic3DHminusFourWeight k) : ℂ) /
    (Real.sqrt (periodic3DHminusThreeWeight k) : ℂ)) * _ = _
  field_simp
  <;> ring

end Pphi2Clean.Continuum
