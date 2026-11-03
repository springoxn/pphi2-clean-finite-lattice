import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransform
open scoped FourierTransform
noncomputable section

-- What is the exact Gaussian-Fourier statement?
#print fourier_gaussian_innerProductSpace

-- cpow / npow interplay on positive reals coerced to ℂ
example (t : ℝ) (ht : 0 < t) :
    ((4 * Real.pi * t : ℝ) : ℂ) ^ (2 : ℂ) = (((4 * Real.pi * t : ℝ) ^ 2 : ℝ) : ℂ) := by
  have htwo : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  rw [htwo, Complex.cpow_natCast]
  exact (Complex.ofReal_pow (4 * Real.pi * t) 2).symm

#check Complex.cpow_natCast
#check Complex.ofReal_pow
#check Real.rpow_natCast

-- flip / smul pairing lemmas available
#print VectorFourier.integral_fourierIntegral_smul_eq_flip
#check VectorFourier.fourierIntegral_const_smul
