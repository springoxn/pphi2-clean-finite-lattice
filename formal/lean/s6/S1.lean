import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import S6Isserlis.S3
import S6Isserlis.S1a

/-!
# S1 formalized — distribution-level identification of the position kernel

Paper proofs (`critic ACCEPT`, frontier `FRONTIER_S1_DISTRIBUTION_IDENTIFICATION`):
`proofs/s1_local_integrability_tempered.md`, `proofs/s1_fourier_weak_identity.md`,
`proofs/s1_remove_regularizer.md`.

Statement (weak form, `(2π)`-normalized Schwartz convention of `S6Isserlis.S3`): for
`m > 0` and every test function `φ ∈ 𝓢(V, ℂ)`,

    ⟨𝓕⁻[q], φ⟩ = ∫ c(x) φ(x) dx

with `q(p) = 1/(m² + (2π)²‖p‖²)` and `c(x) = (1/16π²) · aIntegral(m, ‖x‖)` the
Schwinger-parameter position kernel (the definitional object; the `K₁` closed form
`mK₁(mr)/(4π²r)` stays a documented remark since Mathlib has no `BesselK`).

This file develops the analytical ingredients of the paper proof (no `sorry`):
`posKernel` / `heatKernel` definitions, `posKernel_eq_heatParam`, the Gaussian-Fourier
identity `heatGaussian_fourier`, and the fundamental t-integral
`∫₀^∞ e^{−sc} ds = 1/c`.  The parameter-Fubini assembly of the full weak form is built
on top of these.
-/

open SchwartzMap MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace
open Laplacian LineDeriv Real

noncomputable section

namespace S6Isserlis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [(volume : Measure V).HasTemperateGrowth]

/-- The S1 position-space kernel: `c(v) = (1/16π²) · aIntegral(m, ‖v‖)`. -/
def posKernel (m : ℝ) (v : V) : ℝ :=
  (1 / (16 * Real.pi ^ 2)) * Schwinger.aIntegral m ‖v‖

/-- Heat kernel `H_t(v) = (4πt)^{−2} exp(−‖v‖²/(4t))` (real-valued). -/
def heatKernel (t : ℝ) (v : V) : ℝ :=
  ((4 * Real.pi * t) ^ 2)⁻¹ * Real.exp (-(‖v‖ ^ 2) / (4 * t))

/-- The complex Gaussian factor `exp(−‖v‖²/(4t))`. -/
def heatGaussian (t : ℝ) (v : V) : ℂ :=
  Complex.exp (Complex.ofReal (-(‖v‖ ^ 2) / (4 * t)))

/-- The complex Fourier-side factor `exp(−4π²t‖w‖²)`. -/
def heatFourierSide (t : ℝ) (w : V) : ℂ :=
  Complex.exp (-((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * ↑‖w‖ ^ 2)

/-- Real heat kernel, coerced to `ℂ`. -/
def heatKernelCplx (t : ℝ) (v : V) : ℂ :=
  (heatKernel t v : ℂ)

/-! ## 1. `posKernel` equals the heat-parameter integral -/

lemma heatKernel_eq_const_mul (t : ℝ) (v : V) :
    heatKernel t v =
      (1 / (16 * Real.pi ^ 2)) * (t⁻¹) ^ 2 * Real.exp (-(‖v‖ ^ 2) / (4 * t)) := by
  unfold heatKernel
  have hpow : ((4 * Real.pi * t) ^ 2)⁻¹ = (1 / (16 * Real.pi ^ 2)) * (t⁻¹) ^ 2 := by
    rw [← inv_pow]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hpow]

lemma exp_neg_sub_eq (a b : ℝ) : Real.exp (-a - b) = Real.exp (-a) * Real.exp (-b) := by
  rw [← Real.exp_add]
  rw [sub_eq_add_neg]

lemma posKernel_eq_heatParam (m : ℝ) (v : V) :
    posKernel m v = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(m ^ 2 * t)) * heatKernel t v := by
  unfold posKernel
  rw [Schwinger.aIntegral]
  rw [← integral_const_mul]
  apply congrArg (MeasureTheory.integral (volume.restrict (Set.Ioi (0 : ℝ))))
  funext t
  rw [heatKernel_eq_const_mul]
  rw [exp_neg_sub_eq (m ^ 2 * t) (‖v‖ ^ 2 / (4 * t))]
  have hc : (1 / (16 * Real.pi ^ 2)) * (t⁻¹) ^ 2 = ((4 * Real.pi * t) ^ 2)⁻¹ := by
    rw [← inv_pow]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hc]
  ring_nf

/-! ## 2. Gaussian Fourier transform of the heat kernel -/

lemma heatGaussian_fourier (t : ℝ) (ht : 0 < t) (w : V) (hfin : Module.finrank ℝ V = 4) :
    𝓕 (fun v : V ↦ heatGaussian t v) w =
      ((4 * Real.pi * t : ℝ) : ℂ) ^ (2 : ℂ) * heatFourierSide t w := by
  unfold heatGaussian heatFourierSide
  let b : ℂ := ((1 / (4 * t) : ℝ) : ℂ)
  have hne : (4 * t : ℝ) ≠ 0 := by positivity
  have hb : 0 < b.re := by
    dsimp [b]
    positivity
  have hF := fourier_gaussian_innerProductSpace (b := b) (hb := hb) (w := w)
  have hg : (fun v : V ↦ Complex.exp (Complex.ofReal (-(‖v‖ ^ 2) / (4 * t)))) =
      (fun v : V ↦ Complex.exp (-b * ↑‖v‖ ^ 2)) := by
    funext v
    congr 1
    dsimp [b]
    norm_num
    field_simp [Complex.ofReal_ne_zero.mpr hne]
  have hcoef_real : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
    field_simp [hne]
  have hcoef_base : (↑π / b) = ((4 * Real.pi * t : ℝ) : ℂ) := by
    dsimp [b]
    rw [← Complex.ofReal_div]
    exact congrArg Complex.ofReal hcoef_real
  have hexp_arg : -↑π ^ 2 * ↑‖w‖ ^ 2 / b = -((4 * Real.pi ^ 2 * t : ℝ) : ℂ) * ↑‖w‖ ^ 2 := by
    dsimp [b]
    rw [neg_mul, neg_div]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div]
    rw [neg_mul, ← Complex.ofReal_mul]
    congr 1
    congr 1
    field_simp [hne]
  have hfin4 : (↑(Module.finrank ℝ V) / 2 : ℂ) = 2 := by
    rw [hfin]
    norm_num
  rw [hg]
  rw [hF]
  rw [hfin4]
  rw [hcoef_base, hexp_arg]

/-! ## 3. The fundamental t-integral `∫₀^∞ e^{−sc} ds = 1/c` -/

lemma Ioi_integral_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(c * s))) = c⁻¹ := by
  rw [integral_comp_mul_left_Ioi (g := fun x : ℝ => Real.exp (-x)) (a := 0) (b := c) hc]
  rw [mul_zero]
  rw [integral_exp_neg_Ioi_zero]
  simp

lemma Ioi_integral_cexp_neg_mul (c : ℝ) (hc : 0 < c) :
    (∫ s in Set.Ioi (0 : ℝ), Complex.exp (-(c : ℂ) * (s : ℂ))) = (c⁻¹ : ℂ) := by
  have hreal := Ioi_integral_exp_neg_mul c hc
  calc
    (∫ s in Set.Ioi (0 : ℝ), Complex.exp (-(c : ℂ) * (s : ℂ))) =
        (∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(c * s)) : ℂ)) := by
          apply congrArg (MeasureTheory.integral (volume.restrict (Set.Ioi (0 : ℝ))))
          funext s
          have harg : -(c : ℂ) * (s : ℂ) = (↑(-(c * s)) : ℂ) := by norm_num
          rw [harg, ← Complex.ofReal_exp]
    _ = ↑(∫ s in Set.Ioi (0 : ℝ), Real.exp (-(c * s))) := by
          exact (integral_ofReal (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun s : ℝ => Real.exp (-(c * s))))
    _ = (c⁻¹ : ℂ) := by rw [hreal, Complex.ofReal_inv]

/-! ## 4. The q-pairing side (reuse of `S6Isserlis.S3`) -/

/-- `G = 𝓕⁻[q]` applied to a test function is the integral pairing with `q`. -/
lemma greenDistribution_apply (m : ℝ) (hm : 0 < m)
    (hq : (fun p : V ↦ (((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth)
    (φ : 𝓢(V, ℂ)) :
    (greenDistribution m hm hq) φ =
      ∫ p : V, (𝓕⁻ φ) p * ((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℂ) := by
  unfold greenDistribution
  rw [TemperedDistribution.fourierInv_apply]
  simp [Function.HasTemperateGrowth.toTemperedDistribution_apply, smul_eq_mul]

end S6Isserlis