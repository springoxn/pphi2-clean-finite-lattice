import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open SchwartzMap MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace RealInnerProductSpace
open Real

noncomputable section

namespace Probe5

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

-- raw-level self-adjointness / Fourier integral swap
#check VectorFourier.integral_bilin_fourierIntegral_eq_flip
#check VectorFourier.integral_fourierIntegral_smul_eq_flip
#check VectorFourier.fourierIntegral_convergent_iff
#check Real.continuous_fourierChar
#check Real.fourierChar_apply
#check innerₗ
#check continuous_inner

-- gaussian integrability at raw level
#check GaussianFourier.integrable_cexp_neg_mul_sq_norm
#check GaussianFourier.integral_cexp_neg_mul_sq_norm
#check fourier_gaussian_innerProductSpace
#check fourier_gaussian_innerProductSpace'

-- SchwartzMap integrability as raw function / Fourier coe
#check SchwartzMap.integrable
#check fourier_coe
#check fourierInv_coe
#check Real.fourier_eq
#check FourierTransform.fourier_eq
#check VectorFourier.norm_fourierIntegral_le_integral_norm

-- product integrability
#check Integrable.mul
#check Integrable.norm
#check Integrable.mul_prod
#check Integrable.const_mul

-- What are the real-argument gaussian lemmas actually named?
-- Probe: look for the real-valued gaussian integrability.
#check fourier_gaussian_pi

end Probe5
