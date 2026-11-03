import Mathlib
import S6Isserlis.S1
import S6Isserlis.S1weak_draft

open SchwartzMap MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace
open Real

noncomputable section

namespace HeatDual

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [(volume : Measure V).HasTemperateGrowth]

open S6Isserlis

-- check flip_innerₗ is available as a simp lemma
#check flip_innerₗ

-- The heat-dual pairing identity, via raw flip + Fourier inversion + Step B.
-- Goal: ∫_v (heatKernel t v : ℂ) * φ v = ∫_p heatFourierSide t p * (𝓕⁻ φ) p.
example (t : ℝ) (ht : 0 < t) (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ)) :
    (∫ v : V, (heatKernel t v : ℂ) * φ v)
      = (∫ p : V, heatFourierSide t p * (𝓕⁻ φ) p) := by
  let f : V → ℂ := fun v ↦ (heatKernel t v : ℂ)
  let g : V → ℂ := fun p ↦ (𝓕⁻ φ) p
  have hf : Integrable f := integrable_heatKernelCplx t ht
  have hg : Integrable g := by
    dsimp [g]
    exact (𝓕⁻ φ).integrable
  -- flip: ∫ (𝓕 f) • g = ∫ f • (𝓕 g), with L.flip = L (flip_innerₗ, simp).
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (V := V) (W := V)
    (L := innerₗ V) (f := f) (g := g)
    Real.continuous_fourierChar continuous_inner hf hg
  -- Fourier inversion for the Schwartz test function φ.
  have hφcont : Continuous (fun x : V => (φ : V → ℂ) x) := φ.continuous
  have hφint : Integrable (fun x : V => (φ : V → ℂ) x) := φ.integrable
  have h𝓕φint : Integrable (𝓕 (fun x : V => (φ : V → ℂ) x)) := (𝓕 φ).integrable
  have hinv : 𝓕 (𝓕⁻ (fun x : V => (φ : V → ℂ) x)) = (fun x : V => (φ : V → ℂ) x) :=
    Continuous.fourier_fourierInv_eq (V := V) (f := fun x : V => (φ : V → ℂ) x) hφcont hφint h𝓕φint
  -- assemble: ∫ f • φ = ∫ f • 𝓕(𝓕⁻φ) = ∫ (𝓕 f) • (𝓕⁻φ) (flip) = ∫ K • (𝓕⁻φ)
  calc
    (∫ v : V, (heatKernel t v : ℂ) * φ v)
        = ∫ v : V, f v * (φ : V → ℂ) v := by
          apply congrArg (MeasureTheory.integral (volume : Measure V))
          funext v
          simp [f, mul_comm]
    _ = ∫ v : V, f v * 𝓕 (𝓕⁻ (fun x : V => (φ : V → ℂ) x)) v := by
          -- 𝓕(𝓕⁻φ) = φ pointwise
          congr 1
          funext v
          rw [congr_fun hinv v]
    _ = ∫ p : V, (𝓕 f) p * g p := by
          -- flip with 𝓕 g = 𝓕(𝓕⁻φ) substituted back; hflip is ∫(𝓕f)g = ∫ f(𝓕g)
          sorry
    _ = ∫ p : V, heatFourierSide t p * (𝓕⁻ φ) p := by
          congr 1
          funext p
          rw [heatKernelCplx_fourier_apply t ht hfin p]
          simp [g, f, smul_eq_mul]

end HeatDual
