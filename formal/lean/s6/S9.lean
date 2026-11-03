import Mathlib

/-!
# S9 — OS3: convolution of polynomially decaying functions

Formalizes paper `lem:conv` (`paper/completion/sections/os234.tex`):
if `‖F y‖ ≤ CF (1+‖y‖)^{-N}` and `‖G y‖ ≤ CG (1+‖y‖)^{-N}` with `N > dim E`,
then `y ↦ F y * G (x - y)` is integrable with
`‖∫ y, F y * G (x-y)‖ ≤ 2^N (CF ‖G‖₁ + CG ‖F‖₁) (1+‖x‖)^{-N}`.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace OS3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure] [μ.IsNegInvariant]

/-- `((1+a)/2)^{-N} = 2^N (1+a)^{-N}`. -/
lemma div_two_rpow_neg (a N : ℝ) (ha : 0 ≤ 1 + a) :
    ((1 + a) / 2) ^ (-N) = 2 ^ N * (1 + a) ^ (-N) := by
  rw [div_eq_mul_inv, Real.mul_rpow ha (by norm_num : (0 : ℝ) ≤ 2⁻¹),
    Real.inv_rpow (show (0 : ℝ) ≤ 2 by norm_num) (-N), Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) N,
    inv_inv, mul_comm]

/-- **Convolution of polynomially decaying functions** (paper `lem:conv`). -/
theorem conv_decay {F G : E → ℂ} {CF CG N : ℝ} (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hN : (Module.finrank ℝ E : ℝ) < N)
    (hFm : AEStronglyMeasurable F μ) (hGm : AEStronglyMeasurable G μ)
    (hF : ∀ y, ‖F y‖ ≤ CF * (1 + ‖y‖) ^ (-N))
    (hG : ∀ y, ‖G y‖ ≤ CG * (1 + ‖y‖) ^ (-N)) (x : E) :
    Integrable (fun y => F y * G (x - y)) μ ∧
      ‖∫ y, F y * G (x - y) ∂μ‖ ≤
        2 ^ N * (CF * (∫ y, ‖G y‖ ∂μ) + CG * (∫ y, ‖F y‖ ∂μ)) * (1 + ‖x‖) ^ (-N) := by
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.cast_nonneg _) hN
  have hNneg : -N ≤ 0 := neg_nonpos.mpr hNpos.le
  have hbase : Integrable (fun y : E => (1 + ‖y‖) ^ (-N)) μ :=
    integrable_one_add_norm hN
  have hFint : Integrable F μ :=
    Integrable.mono' (hbase.const_mul CF) hFm (Filter.Eventually.of_forall hF)
  have hGint : Integrable G μ :=
    Integrable.mono' (hbase.const_mul CG) hGm (Filter.Eventually.of_forall hG)
  -- shift measure preservation
  have hGsh_int : Integrable (fun y : E => ‖G (x - y)‖) μ :=
    hGint.norm.comp_sub_left x
  have hGsh_eq : (∫ y : E, ‖G (x - y)‖ ∂μ) = ∫ z, ‖G z‖ ∂μ :=
    integral_sub_left_eq_self (fun z => ‖G z‖) μ x
  -- measurability / integrability of the convolution integrand
  have hmp : MeasurePreserving (fun y : E => x - y) μ μ :=
    Measure.measurePreserving_sub_left μ x
  have hshiftm : AEStronglyMeasurable (fun y : E => G (x - y)) μ :=
    (hmp.aestronglyMeasurable_comp_iff
      (MeasurableEquiv.subLeft x).measurableEmbedding).mpr hGm
  have hprodm : AEStronglyMeasurable (fun y : E => F y * G (x - y)) μ := hFm.mul hshiftm
  have hprodint : Integrable (fun y : E => F y * G (x - y)) μ := by
    refine Integrable.mono' (hbase.const_mul (CF * CG)) hprodm
      (Filter.Eventually.of_forall fun y => ?_)
    have h1 : (1 + ‖x - y‖) ^ (-N) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (le_add_of_nonneg_right (norm_nonneg (x - y))) hNneg
    calc ‖F y * G (x - y)‖ = ‖F y‖ * ‖G (x - y)‖ := norm_mul _ _
      _ ≤ (CF * (1 + ‖y‖) ^ (-N)) * (CG * (1 + ‖x - y‖) ^ (-N)) :=
            mul_le_mul (hF y) (hG (x - y)) (norm_nonneg _)
              (mul_nonneg hCF (Real.rpow_nonneg (by positivity) _))
      _ ≤ (CF * (1 + ‖y‖) ^ (-N)) * (CG * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hCG)
              (mul_nonneg hCF (Real.rpow_nonneg (by positivity) _))
      _ = CF * CG * (1 + ‖y‖) ^ (-N) := by ring
  have hnormint : Integrable (fun y : E => ‖F y‖ * ‖G (x - y)‖) μ := by
    have := hprodint.norm
    simpa only [norm_mul] using this
  -- the splitting set A = {‖x‖/2 ≤ ‖y‖}
  set A : Set E := {y | ‖x‖ / 2 ≤ ‖y‖} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_le measurable_const measurable_norm
  have hsplit : (∫ y : E, ‖F y‖ * ‖G (x - y)‖ ∂μ)
      = (∫ y in A, ‖F y‖ * ‖G (x - y)‖ ∂μ) + ∫ y in Aᶜ, ‖F y‖ * ‖G (x - y)‖ ∂μ :=
    (integral_add_compl hAmeas hnormint).symm
  -- bound on A
  have hAbound : (∫ y in A, ‖F y‖ * ‖G (x - y)‖ ∂μ) ≤
      (2 ^ N * CF * (1 + ‖x‖) ^ (-N)) * ∫ z, ‖G z‖ ∂μ := by
    have hpt : ∀ y ∈ A, ‖F y‖ * ‖G (x - y)‖ ≤
        (2 ^ N * CF * (1 + ‖x‖) ^ (-N)) * ‖G (x - y)‖ := by
      intro y hy
      have hyy : (1 + ‖x‖) / 2 ≤ 1 + ‖y‖ := by
        have h : ‖x‖ / 2 ≤ ‖y‖ := hy
        linarith
      have hstep : (1 + ‖y‖) ^ (-N) ≤ 2 ^ N * (1 + ‖x‖) ^ (-N) := by
        calc (1 + ‖y‖) ^ (-N) ≤ ((1 + ‖x‖) / 2) ^ (-N) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hyy hNneg
          _ = 2 ^ N * (1 + ‖x‖) ^ (-N) := div_two_rpow_neg ‖x‖ N (by positivity)
      calc ‖F y‖ * ‖G (x - y)‖ ≤ (CF * (1 + ‖y‖) ^ (-N)) * ‖G (x - y)‖ :=
            mul_le_mul_of_nonneg_right (hF y) (norm_nonneg _)
        _ ≤ (CF * (2 ^ N * (1 + ‖x‖) ^ (-N))) * ‖G (x - y)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hCF) (norm_nonneg _)
        _ = (2 ^ N * CF * (1 + ‖x‖) ^ (-N)) * ‖G (x - y)‖ := by ring
    calc (∫ y in A, ‖F y‖ * ‖G (x - y)‖ ∂μ)
        ≤ ∫ y in A, (2 ^ N * CF * (1 + ‖x‖) ^ (-N)) * ‖G (x - y)‖ ∂μ :=
          setIntegral_mono_on hnormint.integrableOn (hGsh_int.const_mul _).integrableOn hAmeas hpt
      _ = (2 ^ N * CF * (1 + ‖x‖) ^ (-N)) * ∫ y in A, ‖G (x - y)‖ ∂μ := integral_const_mul _ _
      _ ≤ (2 ^ N * CF * (1 + ‖x‖) ^ (-N)) * ∫ z, ‖G z‖ ∂μ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc (∫ y in A, ‖G (x - y)‖ ∂μ) ≤ (∫ y : E, ‖G (x - y)‖ ∂μ) :=
                  setIntegral_le_integral hGsh_int (Filter.Eventually.of_forall fun y => norm_nonneg _)
              _ = ∫ z, ‖G z‖ ∂μ := hGsh_eq
  -- bound on Aᶜ
  have hcAbound : (∫ y in Aᶜ, ‖F y‖ * ‖G (x - y)‖ ∂μ) ≤
      (2 ^ N * CG * (1 + ‖x‖) ^ (-N)) * ∫ z, ‖F z‖ ∂μ := by
    have hpt : ∀ y ∈ Aᶜ, ‖F y‖ * ‖G (x - y)‖ ≤
        (2 ^ N * CG * (1 + ‖x‖) ^ (-N)) * ‖F y‖ := by
      intro y hy
      have hyx : ‖x‖ / 2 ≤ ‖x - y‖ := by
        have h : ¬ (‖x‖ / 2 ≤ ‖y‖) := hy
        have h2 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
          calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
            _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
        linarith
      have hyy : (1 + ‖x‖) / 2 ≤ 1 + ‖x - y‖ := by linarith
      have hstep : (1 + ‖x - y‖) ^ (-N) ≤ 2 ^ N * (1 + ‖x‖) ^ (-N) := by
        calc (1 + ‖x - y‖) ^ (-N) ≤ ((1 + ‖x‖) / 2) ^ (-N) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hyy hNneg
          _ = 2 ^ N * (1 + ‖x‖) ^ (-N) := div_two_rpow_neg ‖x‖ N (by positivity)
      calc ‖F y‖ * ‖G (x - y)‖ ≤ ‖F y‖ * (CG * (1 + ‖x - y‖) ^ (-N)) :=
            mul_le_mul_of_nonneg_left (hG (x - y)) (norm_nonneg _)
        _ ≤ ‖F y‖ * (CG * (2 ^ N * (1 + ‖x‖) ^ (-N))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hCG) (norm_nonneg _)
        _ = (2 ^ N * CG * (1 + ‖x‖) ^ (-N)) * ‖F y‖ := by ring
    calc (∫ y in Aᶜ, ‖F y‖ * ‖G (x - y)‖ ∂μ)
        ≤ ∫ y in Aᶜ, (2 ^ N * CG * (1 + ‖x‖) ^ (-N)) * ‖F y‖ ∂μ :=
          setIntegral_mono_on hnormint.integrableOn (hFint.norm.const_mul _).integrableOn
            hAmeas.compl hpt
      _ = (2 ^ N * CG * (1 + ‖x‖) ^ (-N)) * ∫ y in Aᶜ, ‖F y‖ ∂μ := integral_const_mul _ _
      _ ≤ (2 ^ N * CG * (1 + ‖x‖) ^ (-N)) * ∫ z, ‖F z‖ ∂μ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact setIntegral_le_integral hFint.norm (Filter.Eventually.of_forall fun y => norm_nonneg _)
  -- assemble
  refine ⟨hprodint, ?_⟩
  have h1 : ‖∫ y, F y * G (x - y) ∂μ‖ ≤ ∫ y : E, ‖F y‖ * ‖G (x - y)‖ ∂μ := by
    calc ‖∫ y, F y * G (x - y) ∂μ‖ ≤ ∫ y, ‖F y * G (x - y)‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ y : E, ‖F y‖ * ‖G (x - y)‖ ∂μ := by simp only [norm_mul]
  calc ‖∫ y, F y * G (x - y) ∂μ‖
      ≤ (∫ y in A, ‖F y‖ * ‖G (x - y)‖ ∂μ) + ∫ y in Aᶜ, ‖F y‖ * ‖G (x - y)‖ ∂μ := by
        rw [← hsplit]; exact h1
    _ ≤ (2 ^ N * CF * (1 + ‖x‖) ^ (-N)) * ∫ z, ‖G z‖ ∂μ
          + (2 ^ N * CG * (1 + ‖x‖) ^ (-N)) * ∫ z, ‖F z‖ ∂μ := add_le_add hAbound hcAbound
    _ = 2 ^ N * (CF * (∫ y, ‖G y‖ ∂μ) + CG * (∫ y, ‖F y‖ ∂μ)) * (1 + ‖x‖) ^ (-N) := by ring

end OS3
