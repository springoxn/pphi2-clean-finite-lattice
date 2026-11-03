import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open SchwartzMap MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace
open Laplacian LineDeriv Real

noncomputable section

namespace S1Probe

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

-- Gaussian Fourier on inner product space
#check fourier_gaussian_innerProductSpace
#check fourier_gaussian_pi
#check integral_rexp_neg_mul_sq_norm
#check integral_cexp_neg_mul_sq_norm
#check integrable_cexp_neg_mul_sq_norm

-- SchwartzMap self-adjointness / Parseval
#check integral_fourier_mul_eq
#check integral_fourierInv_mul_eq
#check integral_fourier_smul_eq
#check integral_fourierInv_smul_eq
#check FourierTransform.fourier_fourierInv_eq
#check FourierTransform.fourierInv_fourier_eq

-- integrability of SchwartzMap functions
#check SchwartzMap.integrable
#check ContinuousMap.integrable
#check Integrable.mul
#check Integrable.const_mul
#check Integrable.const_smul
#check Integrable.bdd_mul
#check IntegrableOn.mul

-- interval integral ↔ Lebesgue over Ioi
#check intervalIntegral.integral_of_le
#check intervalIntegral.integral_Ioi
#check intervalIntegral.integral_Ioi_of_measurable
#check MeasureTheory.integral_restrict
#check MeasureTheory.integral_mul_integral_of_finset
#check MeasureTheory.integral_prod
#check MeasureTheory.integral_prod_symm
#check MeasureTheory.integral_integral_swap
#check MeasureTheory.lintegral_prod
#check MeasureTheory.integrable_prod

-- exponential t-integral: ∫ e^{-ct} over Ioi
#check integral_exp_neg_mul_const
#check intervalIntegral.integral_exp_neg_mul_const
#check intervalIntegral.integral_exp_neg_lt_top
#check integrableOn_Ioi_exp_neg_mul_const
#check intervalIntegral.integral_exp_neg_mul_Ioi

-- complex exp / coercion utils
#check Complex.exp_zero
#check Complex.ofReal_exp
#check Complex.ofReal_neg
#check Complex.ofReal_div
#check Complex.ofReal_mul
#check Complex.ofReal_pow
#check neg_div
#check div_eq_mul_inv

-- norm / inner product basics
#check sq_norm_eq_inner_self
#check Real.norm_eq_abs
#check norm_smul
#check real_inner_comm

-- measure restrict & density
#check Measure.restrict_apply
#check Measure.restrict_prod
#check Measure.prod_restrict
#check Measure.restrict_comp

-- measurability
#check measurable_exp
#check Continuous.exp
#check Measurable.cexp
#check Continuous.cexp
#check continuous_exp
#check ContMDiff.cexp
#check stronglyMeasurable_exp

end S1Probe