import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import S6Isserlis.S1

open SchwartzMap MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace RealInnerProductSpace
open Real

noncomputable section

namespace S6Isserlis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [(volume : Measure V).HasTemperateGrowth]

/-! ## Step A: the complexified heat kernel is integrable. -/

/-- The complex Gaussian `heatGaussian t` is integrable for `t > 0`. -/
lemma integrable_heatGaussian (t : ℝ) (ht : 0 < t) :
    Integrable (fun v : V ↦ heatGaussian t v) := by
  let b : ℂ := ((1 / (4 * t) : ℝ) : ℂ)
  have hne : (4 * t : ℝ) ≠ 0 := by positivity
  have hb : 0 < b.re := by
    dsimp [b]
    positivity
  have h0 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hb 0 (0 : V)
  have h0' : Integrable (fun v : V ↦ Complex.exp (-b * ↑‖v‖ ^ 2)) := by
    simpa using h0
  have hg : (fun v : V ↦ heatGaussian t v) =
      (fun v : V ↦ Complex.exp (-b * ↑‖v‖ ^ 2)) := by
    funext v
    unfold heatGaussian
    congr 1
    dsimp [b]
    norm_num
    field_simp [Complex.ofReal_ne_zero.mpr hne]
  rwa [hg]

/-- Pointwise shape: `↑(heatKernel t v) = ((4πt)²)⁻¹ * heatGaussian t v`. -/
lemma heatKernelCplx_eq (t : ℝ) (v : V) :
    (heatKernel t v : ℂ) = ((((4 * Real.pi * t) ^ 2)⁻¹ : ℝ) : ℂ) * heatGaussian t v := by
  unfold heatKernel heatGaussian
  rw [Complex.ofReal_mul]
  rw [Complex.ofReal_exp]

/-- The complexified heat kernel is integrable for `t > 0`. -/
lemma integrable_heatKernelCplx (t : ℝ) (ht : 0 < t) :
    Integrable (fun v : V ↦ (heatKernel t v : ℂ)) := by
  have hshape : (fun v : V ↦ (heatKernel t v : ℂ)) =
      (fun v : V ↦ ((((4 * Real.pi * t) ^ 2)⁻¹ : ℝ) : ℂ) • heatGaussian t v) := by
    funext v
    rw [heatKernelCplx_eq]
    simp [smul_eq_mul]
  rw [hshape]
  exact Integrable.smul ((((4 * Real.pi * t) ^ 2)⁻¹ : ℝ) : ℂ) (integrable_heatGaussian t ht)

/-! ## Step B: the raw Fourier transform of the complexified heat kernel is `heatFourierSide t`. -/

/-- Function-level shape: `(heatKernel t : V → ℂ) = c • (heatGaussian t : V → ℂ)`, with
`c = ↑(((4πt)²)⁻¹)`.  This *function-level* smul form is what makes
`VectorFourier.fourierIntegral_const_smul` (pattern `r • f`) fire. -/
lemma heatKernelCplx_eq_smul (t : ℝ) :
    (fun v : V ↦ (heatKernel t v : ℂ)) =
      (((((4 * Real.pi * t) ^ 2)⁻¹ : ℝ) : ℂ) • fun v : V ↦ heatGaussian t v) := by
  funext v
  unfold heatKernel heatGaussian
  simp [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_pow, Complex.ofReal_inv]

/-- `(↑(4πt)) ^ (2 : ℂ) = ↑((4πt)²)` for `t > 0`: the cpow (2:ℂ) of a positive real
coerced to `ℂ` is the coerced real square. -/
lemma heatCoef_cpow_two (t : ℝ) (ht : 0 < t) :
    ((4 * Real.pi * t : ℝ) : ℂ) ^ (2 : ℂ) = (((4 * Real.pi * t : ℝ) ^ 2 : ℝ) : ℂ) := by
  have htwo : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  rw [htwo, Complex.cpow_natCast]
  exact (Complex.ofReal_pow (4 * Real.pi * t) 2).symm

/-- Raw Fourier of the full heat kernel (finrank 4), pointwise:
`𝓕 (fun v ↦ (heatKernel t v : ℂ)) w = heatFourierSide t w` = `exp(-4π²t‖w‖²)`. -/
lemma heatKernelCplx_fourier_apply (t : ℝ) (ht : 0 < t) (hfin : Module.finrank ℝ V = 4)
    (w : V) :
    𝓕 (fun v : V ↦ (heatKernel t v : ℂ)) w = heatFourierSide t w := by
  let c : ℂ := ((((4 * Real.pi * t) ^ 2)⁻¹ : ℝ) : ℂ)
  have hshape : (fun v : V ↦ (heatKernel t v : ℂ)) = c • (fun v : V ↦ heatGaussian t v) := by
    simpa [c] using heatKernelCplx_eq_smul t
  rw [hshape]
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ V)
    (c • (fun v : V ↦ heatGaussian t v)) w = heatFourierSide t w
  rw [VectorFourier.fourierIntegral_const_smul]
  rw [Pi.smul_apply]
  change c • 𝓕 (fun v : V ↦ heatGaussian t v) w = heatFourierSide t w
  have hF := heatGaussian_fourier t ht w hfin
  rw [hF]
  rw [smul_eq_mul]
  rw [← mul_assoc]
  have hcpos : 0 < (4 * Real.pi * t : ℝ) := by positivity
  have hcancel : c * (((4 * Real.pi * t : ℝ) : ℂ) ^ (2 : ℂ)) = (1 : ℂ) := by
    rw [heatCoef_cpow_two t ht]
    dsimp [c]
    rw [← Complex.ofReal_mul]
    rw [← Complex.ofReal_one]
    rw [Complex.ofReal_inj]
    field_simp [pow_ne_zero 2 (ne_of_gt hcpos)]
  rw [hcancel]
  simp

/-- Raw Fourier of the full heat kernel (finrank 4), function level:
`𝓕 (fun v ↦ (heatKernel t v : ℂ)) = heatFourierSide t`. -/
lemma heatKernelCplx_fourier (t : ℝ) (ht : 0 < t) (hfin : Module.finrank ℝ V = 4) :
    (fun w : V ↦ 𝓕 (fun v : V ↦ (heatKernel t v : ℂ)) w) = heatFourierSide t := by
  funext w
  exact heatKernelCplx_fourier_apply t ht hfin w

/-! ## Step C: the x↔t Fubini assembly of the weak form. -/

/-- Complexified pointwise identity: `(posKernel m v : ℂ)` equals the heat-parameter
integral (real heat kernel coerced to `ℂ`).  Direct corollary of
`posKernel_eq_heatParam` (S1) pushed through `integral_ofReal`. -/
lemma posKernel_complex (m : ℝ) (hm : 0 < m) (v : V) :
    (posKernel m v : ℂ) =
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) * (heatKernel t v : ℂ))) := by
  rw [posKernel_eq_heatParam]
  symm
  calc
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) * (heatKernel t v : ℂ)))
        = (∫ t in Set.Ioi (0 : ℝ), (((Real.exp (-(m ^ 2 * t)) * heatKernel t v) : ℝ) : ℂ)) := by
          apply congrArg (MeasureTheory.integral (volume.restrict (Set.Ioi (0 : ℝ))))
          funext t
          rw [← Complex.ofReal_mul]
    _ = ↑(∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) * heatKernel t v)) := by
          exact (integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun t : ℝ => Real.exp (-(m ^ 2 * t)) * heatKernel t v))

/-- Normalization of the real heat kernel: `∫_v heatKernel t v = 1` for `finrank ℝ V = 4`.
The real Gaussian integral `∫_v exp(-‖v‖²/(4t)) = (4πt)²` (finrank 4) combines with the
`((4πt)²)⁻¹` prefactor.  The exponent is an ℝ-power (`rpow` from
`GaussianFourier.integral_rexp_neg_mul_sq_norm`); `Real.rpow_natCast` demotes it. -/
lemma heatKernel_integral (t : ℝ) (ht : 0 < t) (hfin : Module.finrank ℝ V = 4) :
    (∫ v : V, heatKernel t v) = 1 := by
  have hb : 0 < (1 / (4 * t) : ℝ) := by positivity
  have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) hb
  have hg' : (∫ v : V, Real.exp (-‖v‖ ^ 2 / (4 * t))) =
      (π / (1 / (4 * t) : ℝ)) ^ (Module.finrank ℝ V / 2 : ℝ) := by
    calc
      (∫ v : V, Real.exp (-‖v‖ ^ 2 / (4 * t))) = ∫ v : V, Real.exp (-(1 / (4 * t)) * ‖v‖ ^ 2) := by
        apply congrArg (MeasureTheory.integral (volume : Measure V))
        funext v
        congr 1
        field_simp
      _ = (π / (1 / (4 * t) : ℝ)) ^ (Module.finrank ℝ V / 2 : ℝ) := hg
  unfold heatKernel
  rw [MeasureTheory.integral_const_mul]
  rw [hg']
  have hπ : (π / (1 / (4 * t) : ℝ) : ℝ) = 4 * π * t := by
    field_simp [ne_of_gt ht]
  have hfin2 : (Module.finrank ℝ V / 2 : ℝ) = 2 := by
    rw [hfin]
    norm_num
  rw [hπ, hfin2]
  have hc : 0 < (4 * π * t : ℝ) := by positivity
  simp [Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hc))]


/-- The heat kernel (real) is nonnegative. -/
lemma heatKernel_nonneg (t : ℝ) (v : V) : 0 ≤ (heatKernel t v : ℝ) := by
  unfold heatKernel
  positivity

/-- Pointwise bound of a Schwartz test function by its sup norm (`toBoundedContinuousFunction`). -/
lemma phi_sup_bound (φ : 𝓢(V, ℂ)) (v : V) : ‖φ v‖ ≤ ‖φ.toBoundedContinuousFunction‖ := by
  simpa using (BoundedContinuousFunction.norm_coe_le_norm φ.toBoundedContinuousFunction v)

/-- Core integrability bound: `∫_v ‖φ v‖ · (heatKernel t v : ℝ) ≤ ‖φ‖∞ · ∫_v heatKernel t v`.
The heart of the joint-integrability argument: boundedness of `φ` (sup norm) pulls out of
the `v`-integral against the (nonnegative) heat kernel. -/
lemma core_bound (t : ℝ) (ht : 0 < t) (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ)) :
    (∫ v : V, ‖φ v‖ * (heatKernel t v : ℝ))
      ≤ ‖φ.toBoundedContinuousFunction‖ * (∫ v : V, (heatKernel t v : ℝ)) := by
  have hk_int : Integrable (fun v : V => (heatKernel t v : ℝ)) :=
    integrable_of_integral_eq_one (μ := volume) (heatKernel_integral t ht hfin)
  let F : V → ℝ := fun v ↦ ‖φ v‖ * (heatKernel t v : ℝ)
  let B : V → ℝ := fun v ↦ ‖φ.toBoundedContinuousFunction‖ * (heatKernel t v : ℝ)
  have hB_int : Integrable B := by
    dsimp [B]
    exact hk_int.const_mul ‖φ.toBoundedContinuousFunction‖
  have hF_meas : AEStronglyMeasurable F volume := by
    dsimp [F]
    fun_prop
  have hF_int : Integrable F := by
    refine MeasureTheory.Integrable.mono' hB_int hF_meas ?_
    filter_upwards with v
    dsimp [F, B]
    have hnonneg : 0 ≤ ‖φ v‖ * (heatKernel t v : ℝ) :=
      mul_nonneg (norm_nonneg _) (heatKernel_nonneg t v)
    rw [abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_right (phi_sup_bound φ v) (heatKernel_nonneg t v)
  have hF_le_B : F ≤ B := by
    intro v
    dsimp [F, B]
    exact mul_le_mul_of_nonneg_right (phi_sup_bound φ v) (heatKernel_nonneg t v)
  calc
    ∫ v : V, ‖φ v‖ * (heatKernel t v : ℝ) = ∫ v : V, F v := by rfl
    _ ≤ ∫ v : V, B v := integral_mono hF_int hB_int hF_le_B
    _ = ‖φ.toBoundedContinuousFunction‖ * (∫ v : V, heatKernel t v) := by
          dsimp [B]
          rw [MeasureTheory.integral_const_mul]


/-- Norm of the complexified heat kernel equals the real (nonnegative) heat kernel. -/
lemma heatKernelCplx_norm (t : ℝ) (v : V) : ‖(heatKernel t v : ℂ)‖ = (heatKernel t v : ℝ) := by
  calc
    ‖(heatKernel t v : ℂ)‖ = |heatKernel t v| := RCLike.norm_ofReal (K := ℂ) (heatKernel t v)
    _ = heatKernel t v := abs_of_nonneg (heatKernel_nonneg t v)

/-- `e^{-m²t}` is integrable on `(Ioi 0)` for `m > 0`.  Via
`exp_neg_integrableOn_Ioi` (mathlib `MeasureTheory.Integral.ExpDecay`). -/
lemma integrable_exp_m2t (m : ℝ) (hm : 0 < m) :
    Integrable (fun t : ℝ => Real.exp (-(m ^ 2 * t))) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hb : 0 < m ^ 2 := sq_pos_of_pos hm
  have hI := exp_neg_integrableOn_Ioi (0 : ℝ) (b := m ^ 2) hb
  simpa [IntegrableOn, Measure.restrict_restrict, Set.Ioi_inter_Ioi] using hI

/-- Pointwise bound of the inner `v`-integral: for each `t > 0`,
`∫_v ‖e^{-m²t} · ((heatKernel t v : ℂ) · φ v)‖ ≤ ‖φ‖∞ · e^{-m²t}`.
Composed from `core_bound` (boundedness of `φ`) and `heatKernel_integral` (∫_v H_t = 1),
pulling the nonnegative `e^{-m²t}` factor out. -/
lemma heatParam_inner_norm_le (m : ℝ) (hm : 0 < m) (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ))
    (t : ℝ) (ht : 0 < t) :
    (∫ v : V, ‖Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)‖)
      ≤ ‖φ.toBoundedContinuousFunction‖ * Real.exp (-(m ^ 2 * t)) := by
  have hem : 0 ≤ Real.exp (-(m ^ 2 * t)) := (Real.exp_pos _).le
  have hnorm_exp : ‖(Real.exp (-(m ^ 2 * t)) : ℂ)‖ = Real.exp (-(m ^ 2 * t)) := by
    calc
      ‖(Real.exp (-(m ^ 2 * t)) : ℂ)‖ = |Real.exp (-(m ^ 2 * t))| :=
        RCLike.norm_ofReal (K := ℂ) (Real.exp (-(m ^ 2 * t)))
      _ = Real.exp (-(m ^ 2 * t)) := abs_of_nonneg hem
  calc
    (∫ v : V, ‖Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)‖)
        = (∫ v : V, Real.exp (-(m ^ 2 * t)) * ‖(heatKernel t v : ℂ) * φ v‖) := by
          apply congrArg (MeasureTheory.integral (volume : Measure V))
          funext v
          rw [norm_mul, hnorm_exp]
    _ = Real.exp (-(m ^ 2 * t)) * (∫ v : V, ‖(heatKernel t v : ℂ) * φ v‖) := by
          rw [MeasureTheory.integral_const_mul]
    _ ≤ Real.exp (-(m ^ 2 * t)) * (‖φ.toBoundedContinuousFunction‖ * 1) := by
          exact mul_le_mul_of_nonneg_left (by
            calc
              (∫ v : V, ‖(heatKernel t v : ℂ) * φ v‖)
                  = (∫ v : V, ‖φ v‖ * (heatKernel t v : ℝ)) := by
                    apply congrArg (MeasureTheory.integral (volume : Measure V))
                    funext v
                    rw [norm_mul, heatKernelCplx_norm t v]
                    ring
              _ ≤ ‖φ.toBoundedContinuousFunction‖ * (∫ v : V, (heatKernel t v : ℝ)) := core_bound t ht hfin φ
              _ = ‖φ.toBoundedContinuousFunction‖ * 1 := by rw [heatKernel_integral t ht hfin]) hem
    _ = ‖φ.toBoundedContinuousFunction‖ * Real.exp (-(m ^ 2 * t)) := by ring

lemma heat_cont_on (m : ℝ) (φ : 𝓢(V, ℂ)) :
    ContinuousOn (fun p : ℝ × V => (heatKernel p.1 p.2 : ℂ)) {p : ℝ × V | 0 < p.1} := by
  let s : Set (ℝ × V) := {p : ℝ × V | 0 < p.1}
  have hsq : ContinuousOn (fun p : ℝ × V => ((4 * Real.pi * p.1) ^ 2 : ℝ)) s := by
    dsimp [s]
    fun_prop
  have hsq_inv : ContinuousOn (fun p : ℝ × V => (((4 * Real.pi * p.1) ^ 2)⁻¹ : ℝ)) s := by
    refine hsq.inv₀ ?_
    intro p hp
    dsimp [s] at hp
    apply pow_ne_zero 2
    exact ne_of_gt (mul_pos (mul_pos (by positivity) Real.pi_pos) hp)
  have hnum : ContinuousOn (fun p : ℝ × V => (-(‖p.2‖ ^ 2) : ℝ)) s := by
    dsimp [s]
    fun_prop
  have hden : ContinuousOn (fun p : ℝ × V => (4 * p.1 : ℝ)) s := by
    dsimp [s]
    fun_prop
  have hden_inv : ContinuousOn (fun p : ℝ × V => ((4 * p.1 : ℝ)⁻¹)) s := by
    refine hden.inv₀ ?_
    intro p hp
    dsimp [s] at hp
    exact ne_of_gt (mul_pos (by norm_num) hp)
  have harg : ContinuousOn (fun p : ℝ × V => (-(‖p.2‖ ^ 2) / (4 * p.1) : ℝ)) s := by
    convert hnum.mul hden_inv <;> simp [div_eq_mul_inv]
  have hexp : ContinuousOn (fun p : ℝ × V => Real.exp (-(‖p.2‖ ^ 2) / (4 * p.1))) s :=
    Real.continuous_exp.comp_continuousOn harg
  have hprod : ContinuousOn (fun p : ℝ × V => ((4 * Real.pi * p.1) ^ 2)⁻¹ * Real.exp (-(‖p.2‖ ^ 2) / (4 * p.1))) s := by
    exact hsq_inv.mul hexp
  have hc : ContinuousOn (fun p : ℝ × V => ((((4 * Real.pi * p.1) ^ 2)⁻¹ * Real.exp (-(‖p.2‖ ^ 2) / (4 * p.1)) : ℝ) : ℂ)) s :=
    Complex.continuous_ofReal.comp_continuousOn hprod
  simpa [heatKernel] using hc

-- The uncurried norm-integrand is continuous on {t > 0}.
lemma hcont_unc (m : ℝ) (φ : 𝓢(V, ℂ)) :
    ContinuousOn (fun p : ℝ × V => ‖Real.exp (-(m ^ 2 * p.1)) * ((heatKernel p.1 p.2 : ℂ) * φ p.2)‖)
      {p : ℝ × V | 0 < p.1} := by
  let s : Set (ℝ × V) := {p : ℝ × V | 0 < p.1}
  have h_hk := heat_cont_on m φ
  have h_exp : ContinuousOn (fun p : ℝ × V => (Real.exp (-(m ^ 2 * p.1)) : ℂ)) s := by
    dsimp [s]
    fun_prop
  have h_phi : ContinuousOn (fun p : ℝ × V => φ p.2) s := by
    dsimp [s]
    fun_prop
  have hc : ContinuousOn (fun p : ℝ × V => (Real.exp (-(m ^ 2 * p.1)) : ℂ) * ((heatKernel p.1 p.2 : ℂ) * φ p.2)) s := by
    exact h_exp.mul (h_hk.mul h_phi)
  simpa [s] using hc.norm

-- The t-value function ∫_v ‖H t v‖ is integrable on (Ioi 0).
lemma integrable_inner_norm (m : ℝ) (hm : 0 < m) (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ)) :
    Integrable (fun t : ℝ => ∫ v : V, ‖Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  let μt : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hg : Integrable
      (fun t : ℝ => ‖φ.toBoundedContinuousFunction‖ * Real.exp (-(m ^ 2 * t))) μt := by
    dsimp [μt]
    exact (integrable_exp_m2t m hm).const_mul ‖φ.toBoundedContinuousFunction‖
  have hF_ae : AEStronglyMeasurable
      (fun p : ℝ × V => ‖Real.exp (-(m ^ 2 * p.1)) * ((heatKernel p.1 p.2 : ℂ) * φ p.2)‖)
      (μt.prod volume) := by
    have hcont := hcont_unc m φ
    have hs : MeasurableSet ({p : ℝ × V | 0 < p.1} : Set (ℝ × V)) := by
      exact (isOpen_lt continuous_const continuous_fst).measurableSet
    have hae := ContinuousOn.aestronglyMeasurable (μ := μt.prod volume) hcont hs
    have hmeas_eq : (μt.prod volume).restrict {p : ℝ × V | 0 < p.1} = μt.prod volume := by
      dsimp [μt]
      have hB : ({p : ℝ × V | 0 < p.1} : Set (ℝ × V)) = (Set.Ioi (0 : ℝ)) ×ˢ (Set.univ : Set V) := by
        ext p; simp
      rw [hB]
      have h1 : (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure V)
          = (volume.prod volume).restrict ((Set.Ioi (0 : ℝ)) ×ˢ (Set.univ : Set V)) := by
        have hpr := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure V))
          (s := Set.Ioi (0 : ℝ)) (t := Set.univ)
        simpa using hpr
      rw [h1]
      have hBm : MeasurableSet ((Set.Ioi (0 : ℝ)) ×ˢ (Set.univ : Set V)) := by
        exact (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))).prod MeasurableSet.univ
      rw [Measure.restrict_restrict hBm]
      congr 1
      ext p; simp
    rwa [hmeas_eq] at hae
  have hf_meas : AEStronglyMeasurable
      (fun t : ℝ => ∫ v : V, ‖Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)‖)
      μt := by
    exact hF_ae.integral_prod_right'
  have h_ae : ∀ᵐ t ∂μt,
      ‖∫ v : V, ‖Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)‖‖
        ≤ ‖φ.toBoundedContinuousFunction‖ * Real.exp (-(m ^ 2 * t)) := by
    dsimp [μt]
    rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht
    have hnonneg : 0 ≤ (∫ v : V, ‖Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)‖) := by
      exact integral_nonneg (fun v => norm_nonneg _)
    rw [abs_of_nonneg hnonneg]
    exact heatParam_inner_norm_le m hm hfin φ t ht
  exact MeasureTheory.Integrable.mono' hg hf_meas h_ae


/-- Joint integrability of the flipped integrand `H(t,v) = e^{-m²t}·((heatKernel t v : ℂ)·φ v)`
on `(Ioi 0) × V` (outer `t`).  Uses `integrable_prod_iff` (outer α = ℝ): the two clauses are
per-`t` integrability in `v` and the `t`-integrability of `∫_v ‖H t v‖` (the latter is
`integrable_inner_norm`). -/
lemma integrable_uncurryH (m : ℝ) (hm : 0 < m) (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ)) :
    Integrable (Function.uncurry (fun t : ℝ => fun v : V =>
      Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
  let μt : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hpt (t : ℝ) (ht : 0 < t) :
      Integrable (fun v : V => Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)) := by
    have hhk : Integrable (fun v : V => (heatKernel t v : ℂ)) := integrable_heatKernelCplx t ht
    have hgfun : Integrable (fun v : V => ‖φ.toBoundedContinuousFunction‖ * ‖(heatKernel t v : ℂ)‖) :=
      hhk.norm.const_mul ‖φ.toBoundedContinuousFunction‖
    have hprod : Integrable (fun v : V => (heatKernel t v : ℂ) * φ v) := by
      refine MeasureTheory.Integrable.mono' hgfun ?_ ?_
      · fun_prop
      · filter_upwards with v
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (phi_sup_bound φ v) (norm_nonneg _)
    have hc : Integrable (fun v : V => (Real.exp (-(m ^ 2 * t)) : ℂ) * ((heatKernel t v : ℂ) * φ v)) :=
      hprod.const_mul (Real.exp (-(m ^ 2 * t)) : ℂ)
    simpa using hc
  have hH_ae : AEStronglyMeasurable
      (fun p : ℝ × V => (Real.exp (-(m ^ 2 * p.1)) : ℂ) * ((heatKernel p.1 p.2 : ℂ) * φ p.2))
      (μt.prod volume) := by
    let s : Set (ℝ × V) := {p : ℝ × V | 0 < p.1}
    have hcont : ContinuousOn
        (fun p : ℝ × V => (Real.exp (-(m ^ 2 * p.1)) : ℂ) * ((heatKernel p.1 p.2 : ℂ) * φ p.2)) s := by
      have h_hk : ContinuousOn (fun p : ℝ × V => (heatKernel p.1 p.2 : ℂ)) s := by
        simpa [s] using heat_cont_on m φ
      have h_exp : ContinuousOn (fun p : ℝ × V => (Real.exp (-(m ^ 2 * p.1)) : ℂ)) s := by
        dsimp [s]
        fun_prop
      have h_phi : ContinuousOn (fun p : ℝ × V => φ p.2) s := by
        dsimp [s]
        fun_prop
      exact h_exp.mul (h_hk.mul h_phi)
    have hs : MeasurableSet s := by
      dsimp [s]
      exact (isOpen_lt continuous_const continuous_fst).measurableSet
    have hae := ContinuousOn.aestronglyMeasurable (μ := μt.prod volume) hcont hs
    have hmeas_eq : (μt.prod volume).restrict s = μt.prod volume := by
      dsimp [μt, s]
      have hB : ({p : ℝ × V | 0 < p.1} : Set (ℝ × V)) = (Set.Ioi (0 : ℝ)) ×ˢ (Set.univ : Set V) := by
        ext p; simp
      rw [hB]
      have h1 : (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure V)
          = (volume.prod volume).restrict ((Set.Ioi (0 : ℝ)) ×ˢ (Set.univ : Set V)) := by
        have hpr := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure V))
          (s := Set.Ioi (0 : ℝ)) (t := Set.univ)
        simpa using hpr
      rw [h1]
      have hBm : MeasurableSet ((Set.Ioi (0 : ℝ)) ×ˢ (Set.univ : Set V)) := by
        exact (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))).prod MeasurableSet.univ
      rw [Measure.restrict_restrict hBm]
      congr 1
      ext p; simp
    rwa [hmeas_eq] at hae
  have hiff := MeasureTheory.integrable_prod_iff (μ := μt) (ν := volume)
    (f := Function.uncurry (fun t : ℝ => fun v : V =>
      Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v))) hH_ae
  rw [hiff]
  constructor
  · dsimp [μt]
    rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht
    exact hpt t ht
  · simpa [μt] using integrable_inner_norm m hm hfin φ


/-- **X↔t Fubini assembly** (finrank 4, `m > 0`, `φ ∈ 𝓢(V, ℂ)`): the pairing of the
position kernel `posKernel m` against `φ` equals the heat-parameter integral of the
heat-kernel pairing.  Skeleton: `posKernel_complex` substitution, pull `φ v` into the
`t`-integral (`integral_mul_const`), swap `∫_v ∫_t` to `∫_t ∫_v`
(`MeasureTheory.integral_integral_swap`), pull `exp(-m²t)` back out.  The swap needs
joint integrability of the uncurried integrand on `(Ioi 0) × V` (paper `s1_fourier_weak_identity.md`
§2: bounded by `‖φ‖∞ · e^{-m²t} · H_t`, `∫_v H_t = 1` and `∫ e^{-m²t} = 1/m²`). -/
lemma x_t_fubini (m : ℝ) (hm : 0 < m) (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ)) :
    (∫ v : V, (posKernel m v : ℂ) * φ v)
      = ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(m ^ 2 * t)) * (∫ v : V, (heatKernel t v : ℂ) * φ v) := by
  let μt : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let G : V → ℝ → ℂ := fun v t ↦ Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)
  calc
    (∫ v : V, (posKernel m v : ℂ) * φ v)
        = ∫ v : V, (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) * (heatKernel t v : ℂ))) * φ v := by
          apply congrArg (MeasureTheory.integral (volume : Measure V))
          funext v
          rw [posKernel_complex m hm v]
    _ = ∫ v : V, ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)) := by
          apply congrArg (MeasureTheory.integral (volume : Measure V))
          funext v
          rw [← MeasureTheory.integral_mul_const]
          congr 1
          funext t
          ring
    _ = ∫ t in Set.Ioi (0 : ℝ), ∫ v : V, (Real.exp (-(m ^ 2 * t)) * ((heatKernel t v : ℂ) * φ v)) := by
          have hswap := MeasureTheory.integral_integral_swap (α := V) (β := ℝ)
            (μ := volume) (ν := μt) (f := G)
            (by
              have hH := integrable_uncurryH m hm hfin φ
              convert hH.swap using 1
              ext p
              rcases p with ⟨v, t⟩
              rfl)
          simpa [G, μt] using hswap
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(m ^ 2 * t)) * (∫ v : V, (heatKernel t v : ℂ) * φ v) := by
          apply congrArg (MeasureTheory.integral (volume.restrict (Set.Ioi (0 : ℝ))))
          funext t
          rw [MeasureTheory.integral_const_mul]
/-! ## Step D: heat-kernel Fourier duality (raw flip route). -/

/-- Heat-kernel Fourier duality:
`∫_v (heatKernel t v : ℂ) * φ v = ∫_p heatFourierSide t p * (𝓕⁻ φ) p`.
Proved via the raw Fourier self-adjointness `integral_fourierIntegral_smul_eq_flip` with
`L = innerₗ` (whose flip is itself by `flip_innerₗ`), Fourier inversion on the
SchwartzMap `𝓕⁻ φ`, and Step B (`𝓕 (heatKernel t) = heatFourierSide`). -/
lemma heat_dual (t : ℝ) (ht : 0 < t) (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ)) :
    (∫ v : V, (heatKernel t v : ℂ) * φ v)
      = (∫ p : V, heatFourierSide t p * (𝓕⁻ φ) p) := by
  let f : V → ℂ := fun v ↦ (heatKernel t v : ℂ)
  let g : V → ℂ := fun p ↦ (𝓕⁻ φ) p
  have hf : Integrable f := integrable_heatKernelCplx t ht
  have hg : Integrable g := by
    dsimp [g]
    exact (𝓕⁻ φ : 𝓢(V, ℂ)).integrable
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (V := V) (W := V)
    (L := innerₗ V) (f := f) (g := g)
    Real.continuous_fourierChar continuous_inner hf hg
  have hFg (x : V) : VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) g x = φ x := by
    dsimp [g]
    have hfou : 𝓕 ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) = (φ : V → ℂ) := by
      rw [← fourier_coe (𝓕⁻ φ)]
      exact congrArg (fun ψ : 𝓢(V, ℂ) => (ψ : V → ℂ)) (FourierTransform.fourier_fourierInv_eq φ)
    exact congrFun hfou x
  have happly (p : V) : VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f p = heatFourierSide t p := by
    dsimp [f]
    change (𝓕 (fun v : V ↦ (heatKernel t v : ℂ))) p = heatFourierSide t p
    exact heatKernelCplx_fourier_apply t ht hfin p
  have h1 : (∫ v : V, (heatKernel t v : ℂ) * φ v)
      = (∫ v : V, f v • (φ : V → ℂ) v) := by
    apply congrArg (MeasureTheory.integral (volume : Measure V))
    funext v
    simp [f, smul_eq_mul]
  have h2 : (∫ v : V, f v • (φ : V → ℂ) v)
      = (∫ v : V, f v • VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) g v) := by
    apply congrArg (MeasureTheory.integral (volume : Measure V))
    funext v
    rw [hFg v]
  have h3 : (∫ v : V, f v • VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) g v)
      = (∫ ξ : V, VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f ξ • g ξ) := by
    simpa [flip_innerₗ] using hflip.symm
  have h4 : (∫ ξ : V, VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f ξ • g ξ)
      = (∫ p : V, heatFourierSide t p * (𝓕⁻ φ) p) := by
    apply congrArg (MeasureTheory.integral (volume : Measure V))
    funext p
    dsimp [f, g]
    rw [happly]
  rw [h1, h2, h3, h4]

/-! ## Step E: Schwinger representation of the Green multiplier. -/

/-- `q(p) = 1/(m² + (2π)²‖p‖²)` as the t-integral of `e^{-t(m² + (2π)²‖p‖²)}`. -/
lemma q_schwinger (m : ℝ) (hm : 0 < m) (p : V) :
    (∫ t in Set.Ioi (0 : ℝ), Complex.exp (-((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2 : ℝ) : ℂ) * (t : ℂ)))
      = ((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℂ) := by
  have hc : 0 < (m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2 : ℝ) := by
    have hmpos : 0 < (m ^ 2 : ℝ) := sq_pos_of_pos hm
    have hnneg : 0 ≤ (2 * π) ^ 2 * ‖p‖ ^ 2 := by
      exact mul_nonneg (sq_nonneg (2 * π : ℝ)) (sq_nonneg ‖p‖)
    exact add_pos_of_pos_of_nonneg hmpos hnneg
  simpa using (Ioi_integral_cexp_neg_mul (m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2 : ℝ) hc)

/-- Combined real×complex heat-param exponent: `e^{-m²t}·H_t(p) = e^{-t(m² + (2π)²‖p‖²)}`. -/
lemma heatParamFull_exp (m : ℝ) (t : ℝ) (p : V) :
    (Real.exp (-(m ^ 2 * t)) : ℂ) * heatFourierSide t p =
      Complex.exp (-((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2 : ℝ) : ℂ) * (t : ℂ)) := by
  rw [Complex.ofReal_exp]
  unfold heatFourierSide
  rw [← Complex.exp_add]
  congr 1
  ring_nf
  norm_num
  ring

/-- Norm of a coerced real exponential (as `ℂ`) equals the real value. -/
lemma norm_exp_real_coe (x : ℝ) : ‖(Real.exp x : ℂ)‖ = Real.exp x :=
  (RCLike.norm_ofReal (K := ℂ) (Real.exp x)).trans (abs_of_nonneg (Real.exp_pos x).le)

/-- `|H_t(p)| ≤ 1` for `t ≥ 0`: the heat Fourier side is a sub-unital Gaussian. -/
lemma norm_heatFourierSide_le_one (t : ℝ) (ht : 0 ≤ t) (p : V) :
    ‖heatFourierSide t p‖ ≤ 1 := by
  unfold heatFourierSide
  let r : ℝ := -(4 * Real.pi ^ 2 * t * ‖p‖ ^ 2)
  have hexp : -((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * ↑‖p‖ ^ 2 = (r : ℂ) := by
    dsimp [r]
    apply Complex.ext
    · simp
    · simp
  calc
    ‖Complex.exp (-((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * ↑‖p‖ ^ 2)‖
        = ‖Complex.exp (r : ℂ)‖ := by rw [hexp]
    _ = Real.exp (r : ℂ).re := by rw [Complex.norm_exp]
    _ = Real.exp r := by simp
    _ ≤ 1 := by
          apply (Real.exp_le_one_iff).2
          dsimp [r]
          have hp2 : 0 ≤ ‖p‖ ^ 2 := sq_nonneg ‖p‖
          have ht24 : 0 ≤ (4 * π ^ 2 * t) := mul_nonneg (mul_nonneg (by positivity) (sq_nonneg π)) ht
          have h := mul_nonneg ht24 hp2
          linarith

/-- `heatFourierSide` is jointly continuous. -/
lemma continuous_heatFourierSide_joint : Continuous (fun z : ℝ × V => heatFourierSide z.1 z.2) := by
  unfold heatFourierSide
  have h : Continuous (fun z : ℝ × V => -((4 * Real.pi ^ 2 * z.1 : ℝ) : ℂ) * (‖z.2‖ ^ 2 : ℂ)) := by
    continuity
  exact Complex.continuous_exp.comp h

/-- `heatFourierSide t` is continuous in the spatial variable. -/
lemma continuous_heatFourierSide_fun (t : ℝ) : Continuous (fun p : V => heatFourierSide t p) := by
  unfold heatFourierSide
  have h : Continuous (fun p : V => -((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * (‖p‖ ^ 2 : ℂ)) := by
    continuity
  exact Complex.continuous_exp.comp h

/-- `heatFourierSide _ p` is continuous in the parameter. -/
lemma continuous_heatFourierSide_t (p : V) : Continuous (fun t : ℝ => heatFourierSide t p) :=
  continuous_heatFourierSide_joint.comp (continuous_id.prodMk continuous_const)

/-- `(𝓕⁻ φ)` is continuous (SchwartzMap is smooth). -/
lemma continuous_fourierInv_phi (φ : 𝓢(V, ℂ)) :
    Continuous (fun p : V => ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p) :=
  (𝓕⁻ φ : 𝓢(V, ℂ)).continuous

/-- Per-p `t`-integrability of the full heat-param integrand (dominated by `‖(𝓕⁻φ)p‖·e^{-m²t}`). -/
lemma pt_integrable_t_at_p (m : ℝ) (hm : 0 < m) (φ : 𝓢(V, ℂ)) (p : V) :
    Integrable (fun t : ℝ =>
      (Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hdom : Integrable (fun t : ℝ => ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (integrable_exp_m2t m hm).const_mul ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_ ?_)
    · have h : Continuous (fun t : ℝ => (Real.exp (-(m ^ 2 * t)) : ℂ)) := by
        continuity
      exact h.aestronglyMeasurable
    · exact (continuous_heatFourierSide_t p).aestronglyMeasurable
    · have h2 : Continuous (fun t : ℝ => ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p) := continuous_const
      exact h2.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht
    rw [norm_mul, norm_mul, norm_exp_real_coe]
    have hle1 : Real.exp (-(m ^ 2 * t)) * (‖heatFourierSide t p‖ * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖)
        ≤ Real.exp (-(m ^ 2 * t)) * (1 * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (norm_heatFourierSide_le_one t (le_of_lt ht) p) (norm_nonneg _)) (Real.exp_pos _).le
    calc
      Real.exp (-(m ^ 2 * t)) * (‖heatFourierSide t p‖ * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖)
          ≤ Real.exp (-(m ^ 2 * t)) * (1 * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖) := hle1
      _ = ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) := by ring

/-- Per-`t` `p`-integrability on `V` (for `t ≥ 0`): the full heat-param integrand. -/
lemma pt_integrable_at_t (m : ℝ) (φ : 𝓢(V, ℂ)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun p : V => (Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)) := by
  have hp_int : Integrable (fun p : V => ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖) :=
    (𝓕⁻ φ : 𝓢(V, ℂ)).integrable.norm
  refine MeasureTheory.Integrable.mono' hp_int ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_ ?_)
    · exact (continuous_const : Continuous (fun p : V => (Real.exp (-(m ^ 2 * t)) : ℂ))).aestronglyMeasurable
    · exact (continuous_heatFourierSide_fun t).aestronglyMeasurable
    · exact (continuous_fourierInv_phi φ).aestronglyMeasurable
  · filter_upwards with p
    rw [norm_mul, norm_mul, norm_exp_real_coe]
    have hH : ‖heatFourierSide t p‖ ≤ 1 := norm_heatFourierSide_le_one t ht p
    have hle1 : Real.exp (-(m ^ 2 * t)) * (‖heatFourierSide t p‖ * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖)
        ≤ Real.exp (-(m ^ 2 * t)) * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hH (norm_nonneg _))
            (Real.exp_pos _).le
    have hle2 : Real.exp (-(m ^ 2 * t)) * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖
        ≤ ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ := by
          have h₂ : ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) ≤ ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ :=
            mul_le_of_le_one_right (norm_nonneg _) (by
              have hm2t : 0 ≤ m ^ 2 * t := mul_nonneg (sq_nonneg m) ht
              exact (Real.exp_le_one_iff).2 (by linarith))
          simpa [mul_comm] using h₂
    exact hle1.trans hle2



/-- Bound of the inner `p`-norm: `∫_p ‖H·(𝓕⁻φ)‖ ≤ C·e^{-m²t}` with `C = ∫‖(𝓕⁻φ)‖`. -/
lemma pt_inner_norm_le (m : ℝ) (φ : 𝓢(V, ℂ)) (t : ℝ) (ht : 0 ≤ t) :
    (∫ p : V, ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖)
      ≤ (∫ p : V, ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖) * Real.exp (-(m ^ 2 * t)) := by
  have hB_int : Integrable (fun p : V => ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖) :=
    (𝓕⁻ φ : 𝓢(V, ℂ)).integrable.norm
  have hF_int : Integrable (fun p : V =>
      ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖) :=
    (pt_integrable_at_t m φ t ht).norm
  have hle_pt : ∀ᵐ p ∂volume,
      ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖
        ≤ ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) := by
    filter_upwards with p
    rw [norm_mul, norm_mul, norm_exp_real_coe]
    have hH : ‖heatFourierSide t p‖ ≤ 1 := norm_heatFourierSide_le_one t ht p
    have h1 : Real.exp (-(m ^ 2 * t)) * (‖heatFourierSide t p‖ * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖)
        ≤ Real.exp (-(m ^ 2 * t)) * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hH (norm_nonneg _))
            (Real.exp_pos _).le
    calc
      Real.exp (-(m ^ 2 * t)) * (‖heatFourierSide t p‖ * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖)
          ≤ Real.exp (-(m ^ 2 * t)) * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ := h1
      _ = ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) := by ring
  have hR : (∫ p : V, ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)))
        = (∫ p : V, ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖) * Real.exp (-(m ^ 2 * t)) := by
        rw [MeasureTheory.integral_mul_const]
  calc
    (∫ p : V, ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖)
        ≤ ∫ p : V, ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) := by
          exact integral_mono_ae hF_int (hB_int.mul_const _) hle_pt
    _ = (∫ p : V, ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖) * Real.exp (-(m ^ 2 * t)) := hR

/-- Joint integrability of the (p,t)-uncurried heat-param integrand on `V × (Ioi 0)`. -/
lemma pt_joint_integrable (m : ℝ) (hm : 0 < m) (φ : 𝓢(V, ℂ)) :
    Integrable (Function.uncurry (fun p : V => fun t : ℝ =>
      (Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  let μt : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let F : V × ℝ → ℂ := fun z =>
    (Real.exp (-(m ^ 2 * z.2)) : ℂ) * (heatFourierSide z.2 z.1 * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) z.1)
  change Integrable F (volume.prod μt)
  have hF_ae : AEStronglyMeasurable F (volume.prod μt) := by
    dsimp [F]
    have h1 : Continuous (fun z : V × ℝ => (Real.exp (-(m ^ 2 * z.2)) : ℂ)) := by
      continuity
    have h2 : Continuous (fun z : V × ℝ => heatFourierSide z.2 z.1) :=
      continuous_heatFourierSide_joint.comp (continuous_snd.prodMk continuous_fst)
    have h3 : Continuous (fun z : V × ℝ => ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) z.1) :=
      (continuous_fourierInv_phi φ).comp continuous_fst
    exact (h1.mul (h2.mul h3)).aestronglyMeasurable
  rw [integrable_prod_iff hF_ae]
  constructor
  · apply ae_of_all
    intro p
    dsimp [F]
    exact pt_integrable_t_at_p m hm φ p
  · have hle_raw : ∀ᵐ p ∂volume,
        (∫ t : ℝ, ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖ ∂μt)
          ≤ ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * (m ^ 2)⁻¹ := by
      filter_upwards with p
      have hle_t : ∀ᵐ t ∂μt,
          ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖
            ≤ ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) := by
        rw [ae_restrict_iff' measurableSet_Ioi]
        apply ae_of_all
        intro t ht
        rw [norm_mul, norm_mul, norm_exp_real_coe]
        calc
          Real.exp (-(m ^ 2 * t)) * (‖heatFourierSide t p‖ * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖)
              ≤ Real.exp (-(m ^ 2 * t)) * (1 * ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (norm_heatFourierSide_le_one t (le_of_lt ht) p) (norm_nonneg _))
                  (Real.exp_pos _).le
          _ = ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) := by ring
      have hF_t : Integrable (fun t : ℝ => ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖) μt :=
        (pt_integrable_t_at_p m hm φ p).norm
      have hdom_t : Integrable (fun t : ℝ => ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t))) μt := by
        dsimp [μt]
        exact (integrable_exp_m2t m hm).const_mul ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖
      have hint_le : (∫ t : ℝ, ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖ ∂μt)
          ≤ (∫ t : ℝ, ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) ∂μt) :=
        integral_mono_ae hF_t hdom_t hle_t
      have hint_t : ∫ t : ℝ, Real.exp (-(m ^ 2 * t)) ∂μt = (m ^ 2)⁻¹ := by
        dsimp [μt]
        exact Ioi_integral_exp_neg_mul (m ^ 2) (sq_pos_of_pos hm)
      calc
        (∫ t : ℝ, ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖ ∂μt)
            ≤ ∫ t : ℝ, ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * Real.exp (-(m ^ 2 * t)) ∂μt := hint_le
        _ = ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * (∫ t : ℝ, Real.exp (-(m ^ 2 * t)) ∂μt) := by
              exact (MeasureTheory.integral_const_mul ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ (fun t : ℝ => Real.exp (-(m ^ 2 * t))))
        _ = ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * (m ^ 2)⁻¹ := by rw [hint_t]
    have hdom_p : Integrable (fun p : V => ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * (m ^ 2)⁻¹) :=
      (𝓕⁻ φ : 𝓢(V, ℂ)).integrable.norm.mul_const (m ^ 2)⁻¹
    have hmeas_p : AEStronglyMeasurable
        (fun p : V => ∫ t : ℝ, ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖ ∂μt)
        volume :=
      hF_ae.norm.integral_prod_right'
    have hle : ∀ᵐ p ∂volume,
        ‖∫ t : ℝ, ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖ ∂μt‖
          ≤ ‖((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p‖ * (m ^ 2)⁻¹ := by
      filter_upwards [hle_raw] with p hp
      have hnonneg : 0 ≤ (∫ t : ℝ, ‖(Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)‖ ∂μt) := by
        exact integral_nonneg (fun t => norm_nonneg _)
      rwa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact MeasureTheory.Integrable.mono' hdom_p hmeas_p hle

/-- p↔t Fubini swap for the heat-param integrand. -/
lemma p_t_fubini (m : ℝ) (hm : 0 < m) (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ)) :
    (∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-(m ^ 2 * t)) : ℂ) * (∫ p : V, heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p))
      = (∫ p : V,
          (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) : ℂ) * heatFourierSide t p) * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p) := by
  calc
    (∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-(m ^ 2 * t)) : ℂ) * (∫ p : V, heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p))
        = ∫ t in Set.Ioi (0 : ℝ), ∫ p : V,
            (Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p) := by
          apply congrArg (MeasureTheory.integral (volume.restrict (Set.Ioi (0 : ℝ))))
          funext t
          rw [MeasureTheory.integral_const_mul]
    _ = ∫ p : V, ∫ t in Set.Ioi (0 : ℝ),
            (Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p) := by
          have hswap := MeasureTheory.integral_integral_swap (α := V) (β := ℝ)
            (μ := volume) (ν := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun p : V => fun t : ℝ =>
              (Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p))
            (pt_joint_integrable m hm φ)
          exact hswap.symm
    _ = ∫ p : V, (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) : ℂ) * heatFourierSide t p) * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p := by
          apply congrArg (MeasureTheory.integral (volume : Measure V))
          funext p
          calc
            ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) : ℂ) * (heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)
                = ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(m ^ 2 * t)) : ℂ) * heatFourierSide t p) * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p := by
                  apply congrArg (MeasureTheory.integral (volume.restrict (Set.Ioi (0 : ℝ))))
                  funext t
                  rw [mul_assoc]
            _ = (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) : ℂ) * heatFourierSide t p) * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p := by
                  rw [MeasureTheory.integral_mul_const]
/-- **S1 weak-form final assembly.** -/
lemma s1_weak_form (m : ℝ) (hm : 0 < m) (hfin : Module.finrank ℝ V = 4)
    (φ : 𝓢(V, ℂ)) (hq : (fun p : V ↦ (((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth) :
    (∫ v : V, (posKernel m v : ℂ) * φ v) = (greenDistribution m hm hq) φ := by
  calc
    (∫ v : V, (posKernel m v : ℂ) * φ v)
        = ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) : ℂ) * (∫ v : V, (heatKernel t v : ℂ) * φ v) :=
          (x_t_fubini m hm hfin φ)
    _ = ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) : ℂ) * (∫ p : V, heatFourierSide t p * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p) := by
          refine integral_congr_ae ?_
          have hmem : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), t ∈ Set.Ioi (0 : ℝ) :=
            ae_restrict_mem measurableSet_Ioi
          filter_upwards [hmem] with t ht
          rw [heat_dual t ht hfin φ]
    _ = ∫ p : V, (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(m ^ 2 * t)) : ℂ) * heatFourierSide t p) * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p := by
          rw [p_t_fubini m hm hfin φ]
    _ = ∫ p : V, (∫ t in Set.Ioi (0 : ℝ),
            Complex.exp (-((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2 : ℝ) : ℂ) * (t : ℂ))) * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p := by
          apply congrArg (MeasureTheory.integral (volume : Measure V))
          funext p
          apply congrArg (fun h : ℝ → ℂ => (∫ t in Set.Ioi (0 : ℝ), h t) * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p)
          funext t
          exact heatParamFull_exp m t p
    _ = ∫ p : V, ((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℂ) * ((𝓕⁻ φ : 𝓢(V, ℂ)) : V → ℂ) p := by
          apply congrArg (MeasureTheory.integral (volume : Measure V))
          funext p
          rw [q_schwinger m hm p]
    _ = (greenDistribution m hm hq) φ := by
          rw [greenDistribution_apply m hm hq φ]
          apply congrArg (MeasureTheory.integral (volume : Measure V))
          funext p
          rw [mul_comm]

end S6Isserlis