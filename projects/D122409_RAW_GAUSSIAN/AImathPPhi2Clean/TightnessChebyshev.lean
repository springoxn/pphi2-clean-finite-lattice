import Mathlib

noncomputable section

namespace Pphi2Clean.Continuum

open MeasureTheory

theorem second_moment_tail_bound
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (R : ℝ)
    (hR : 0 < R) (hf : Integrable (fun x => f x ^ 2) μ) :
    μ {x | R ≤ |f x|} ≤
      ENNReal.ofReal (∫ x, f x ^ 2 / R ^ 2 ∂μ) := by
  have hg_int : Integrable (fun x => f x ^ 2 / R ^ 2) μ := hf.div_const _
  have hg_nonneg : 0 ≤ᵐ[μ] (fun x => f x ^ 2 / R ^ 2) :=
    Filter.Eventually.of_forall (fun x => by positivity)
  apply hg_int.measure_le_integral hg_nonneg
  intro x hx
  have hprod : 0 ≤ (|f x| - R) * (|f x| + R) := by
    exact mul_nonneg (sub_nonneg.mpr hx) (by positivity)
  exact (le_div_iff₀ (sq_pos_of_pos hR)).2 (by
    nlinarith [sq_abs (f x)])

/-- A uniform second-moment bound gives one tail bound for every member of a
measure family. -/
theorem uniform_second_moment_tail_bound
    {ι X : Type*} [MeasurableSpace X]
    (μ : ι → Measure X) (f : X → ℝ) (R C : ℝ)
    (hR : 0 < R)
    (h_int : ∀ i, Integrable (fun x => f x ^ 2) (μ i))
    (h_moment : ∀ i, ∫ x, f x ^ 2 ∂(μ i) ≤ C) :
    ∀ i, μ i {x | R ≤ |f x|} ≤ ENNReal.ofReal (C / R ^ 2) := by
  intro i
  calc
    μ i {x | R ≤ |f x|} ≤
        ENNReal.ofReal (∫ x, f x ^ 2 / R ^ 2 ∂(μ i)) :=
      second_moment_tail_bound (μ i) f R hR (h_int i)
    _ = ENNReal.ofReal ((∫ x, f x ^ 2 ∂(μ i)) / R ^ 2) := by
      rw [integral_div]
    _ ≤ ENNReal.ofReal (C / R ^ 2) := by
      apply ENNReal.ofReal_mono
      exact div_le_div_of_nonneg_right (h_moment i) (sq_nonneg R)

end Pphi2Clean.Continuum
