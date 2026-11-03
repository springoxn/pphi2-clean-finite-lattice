import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import S6Isserlis.S1

open SchwartzMap MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace RealInnerProductSpace
open Real

noncomputable section

namespace Probe6

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [(volume : Measure V).HasTemperateGrowth]

open S6Isserlis

-- Does the raw-level gaussian integrability lemma work for our gaussian?
-- exp(-‖v‖²/(4t)) = exp(-(1/(4t))*‖v‖²)
-- integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : V)  (c=0,w=0) gives integrable (fun v => cexp (-b*‖v‖²))
example (t : ℝ) (ht : 0 < t) :
    Integrable (fun v : V ↦ Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * ↑‖v‖ ^ 2)) := by
  -- this is the integrability of the gaussian; extract from integral_cexp_neg_mul_sq_norm via
  -- integrable of the integrand? The integral lemma doesn't supply integrability directly.
  -- Use integrable_cexp_neg_mul_sq_norm_add which is a theorem *about* integrability.
  have hb : 0 < ((1 / (4 * t) : ℝ) : ℂ).re := by
    dsimp
    positivity
  exact GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hb 0 (0 : V)

-- Equivalence of the gaussian shapes
example (t : ℝ) (v : V) :
    Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * ↑‖v‖ ^ 2) =
      Complex.exp (Complex.ofReal (-(‖v‖ ^ 2) / (4 * t))) := by
  congr 1
  -- (-(1/(4t))) * ‖v‖^2  vs  -(‖v‖^2/(4t)) as complex
  norm_num
  field_simp
  ring

-- Now the heatGaussian_fourier lemma gives 𝓕 (fun v => heatGaussian t v) = ...
-- Test: coercing heatGaussian_fourier to raw function level
example (t : ℝ) (ht : 0 < t) (w : V) (hfin : Module.finrank ℝ V = 4) :
    𝓕 (fun v : V ↦ Complex.exp (Complex.ofReal (-(‖v‖ ^ 2) / (4 * t)))) w =
      ((4 * Real.pi * t : ℝ) : ℂ) ^ (2 : ℂ) * Complex.exp (-((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * ↑‖w‖ ^ 2) := by
  simpa [S6Isserlis.heatGaussian, S6Isserlis.heatFourierSide] using S6Isserlis.heatGaussian_fourier t ht w hfin

end Probe6
