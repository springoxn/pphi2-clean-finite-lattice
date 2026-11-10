import AImathPPhi2Clean.Periodic3DCylinderUniqueness
import AImathPPhi2Clean.PeriodicFS4DProbeMoment

noncomputable section
set_option maxHeartbeats 1000000
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

def periodic3DRestrictFourier (x : FS4HminusFourCompletion) : Periodic3DCompletion :=
  ⟨fun k : Periodic3DIndex => x (periodic3DExtend k), by
    change Memℓp (fun k : Periodic3DIndex => x (periodic3DExtend k)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
    exact ((lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)).comp_injective
      periodic3DExtend_injective⟩

theorem periodic3DRestrictFourier_norm_le (x : FS4HminusFourCompletion) :
    ‖periodic3DRestrictFourier x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hx := lp.norm_rpow_eq_tsum hp x
  have hy := lp.norm_rpow_eq_tsum hp (periodic3DRestrictFourier x)
  norm_num at hx hy
  rw [hx, hy]
  exact Summable.tsum_le_tsum_of_inj periodic3DExtend periodic3DExtend_injective
    (fun k _ => sq_nonneg _) (fun k => le_rfl)
    (by simpa using (lp.memℓp (periodic3DRestrictFourier x)).summable hp)
    (by simpa using (lp.memℓp x).summable hp)

def periodic3DRestrictFourierCLM : FS4HminusFourCompletion →L[ℝ] Periodic3DCompletion :=
  LinearMap.mkContinuous
    { toFun := periodic3DRestrictFourier
      map_add' := by intro x y; apply lp.ext; rfl
      map_smul' := by intro r x; apply lp.ext; rfl }
    1 (by intro x; simpa using periodic3DRestrictFourier_norm_le x)

def periodic3DTargetMap (L : ℝ) (x : FS4HminusFourCompletion) : Periodic3DCompletion :=
  (Real.sqrt L)⁻¹ • periodic3DRestrictFourierCLM x

theorem continuous_periodic3DTargetMap (L : ℝ) : Continuous (periodic3DTargetMap L) := by
  unfold periodic3DTargetMap
  exact (periodic3DRestrictFourierCLM.continuous).const_smul ((Real.sqrt L)⁻¹ : ℝ)

def periodic3DGaussianTargetMeasure (L mass : ℝ) : Measure Periodic3DCompletion :=
  Measure.map (periodic3DTargetMap L) (fs4GaussianCarrierMeasure L mass)

instance periodic3DGaussianTargetMeasure_probability (L mass : ℝ) :
    IsProbabilityMeasure (periodic3DGaussianTargetMeasure L mass) := by
  unfold periodic3DGaussianTargetMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    (continuous_periodic3DTargetMap L).measurable.aemeasurable).2 inferInstance

theorem periodic3DTargetMap_apply (L : ℝ) (x : FS4HminusFourCompletion) (k : Periodic3DIndex) :
    periodic3DTargetMap L x k = ((Real.sqrt L)⁻¹ : ℝ) • x (periodic3DExtend k) := rfl

theorem periodic3DTargetScale_normalization (L : ℝ) (hL : 0 < L) :
    ((Real.sqrt L)⁻¹) ^ 2 * L ^ 4 = L ^ 3 := by
  rw [inv_pow, Real.sq_sqrt hL.le]
  field_simp
  <;> ring

theorem periodic3DExtend_massSymbol (L mass : ℝ) (k : Periodic3DIndex) :
    torusMassSymbol 4 L mass (periodic3DExtend k) = torusMassSymbol 3 L mass k := by
  simp [torusMassSymbol, periodic3DExtend, Fin.sum_univ_succ]

theorem periodic3DGaussianTargetMeasure_canonical_secondMoment
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (k : Periodic3DIndex)
    (hk : fs4CanonicalPairRepresentative (periodic3DExtend k)) :
    (∫ x : Periodic3DCompletion, ‖x k‖ ^ 2 ∂periodic3DGaussianTargetMeasure L mass) =
      periodic3DHminusFourWeight k * (L ^ 3 / torusMassSymbol 3 L mass k) := by
  rw [periodic3DGaussianTargetMeasure,
    integral_map (continuous_periodic3DTargetMap L).measurable.aemeasurable
      (show AEStronglyMeasurable (fun x : Periodic3DCompletion => ‖x k‖ ^ 2)
        (Measure.map (periodic3DTargetMap L) (fs4GaussianCarrierMeasure L mass)) from
        (((periodic3DHminusFour_coordinate_continuous k).norm.pow 2).aestronglyMeasurable))]
  simp only [periodic3DTargetMap_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, fs4GaussianCarrierMeasure_canonical_secondMoment L mass hL hmass _ hk,
    periodic3DExtend_massSymbol]
  change ((Real.sqrt L)⁻¹) ^ 2 *
      (periodic3DHminusFourWeight k * (L ^ 4 / torusMassSymbol 3 L mass k)) = _
  calc
    _ = periodic3DHminusFourWeight k *
      ((((Real.sqrt L)⁻¹) ^ 2 * L ^ 4) / torusMassSymbol 3 L mass k) := by ring
    _ = _ := by rw [periodic3DTargetScale_normalization L hL]

theorem periodic3DGaussianTargetMeasure_zero_re_law
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Measure.map (fun x : Periodic3DCompletion => (x 0).re)
      (periodic3DGaussianTargetMeasure L mass) =
      gaussianReal 0 ⟨L ^ 3 / mass ^ 2, div_nonneg (pow_nonneg hL.le _) (sq_nonneg _)⟩ := by
  have h : HasLaw (fun x : FS4HminusFourCompletion => (x 0).re)
      (gaussianReal 0 ⟨(L ^ 2 / mass) ^ 2, sq_nonneg _⟩)
      (fs4GaussianCarrierMeasure L mass) :=
    ⟨(Complex.continuous_re.comp (fs4HminusFour_coordinate_continuous 0)).measurable.aemeasurable,
      fs4GaussianCarrierMeasure_zero_re_law L mass hL hmass⟩
  have hs := gaussianReal_mul_const h ((Real.sqrt L)⁻¹)
  have hv : (⟨((Real.sqrt L)⁻¹) ^ 2, sq_nonneg _⟩ *
      ⟨(L ^ 2 / mass) ^ 2, sq_nonneg _⟩ : NNReal) =
      ⟨L ^ 3 / mass ^ 2, div_nonneg (pow_nonneg hL.le _) (sq_nonneg _)⟩ := by
    apply Subtype.ext
    change ((Real.sqrt L)⁻¹) ^ 2 * (L ^ 2 / mass) ^ 2 = _
    calc
      _ = (((Real.sqrt L)⁻¹) ^ 2 * L ^ 4) / mass ^ 2 := by ring
      _ = _ := by rw [periodic3DTargetScale_normalization L hL]
  simp only [mul_zero] at hs
  have hsmap := hs.map_eq
  rw [show NNReal.mk (((Real.sqrt L)⁻¹) ^ 2) (sq_nonneg _) *
      ⟨(L ^ 2 / mass) ^ 2, sq_nonneg _⟩ =
      ⟨L ^ 3 / mass ^ 2, div_nonneg (pow_nonneg hL.le _) (sq_nonneg _)⟩ from hv] at hsmap
  rw [periodic3DGaussianTargetMeasure,
    Measure.map_map (show Measurable (fun x : Periodic3DCompletion => (x 0).re) from
      (Complex.continuous_re.comp (periodic3DHminusFour_coordinate_continuous 0)).measurable)
      (continuous_periodic3DTargetMap L).measurable]
  have heq : (fun x : FS4HminusFourCompletion => (periodic3DTargetMap L x 0).re) =
      (fun x : FS4HminusFourCompletion => (x 0).re * (Real.sqrt L)⁻¹) := by
    funext x
    have hz : periodic3DExtend 0 = 0 := by ext i; simp [periodic3DExtend]
    rw [periodic3DTargetMap_apply, hz]
    simp [Complex.real_smul, mul_comm]
  change Measure.map (fun x : FS4HminusFourCompletion => (periodic3DTargetMap L x 0).re) _ = _
  rw [heq]
  exact hsmap

end Pphi2Clean.Continuum


