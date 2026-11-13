import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
noncomputable section
namespace Pphi2Clean.Continuum
open scoped BigOperators
def periodicHMinusTwoWeight (k : Fin 2 → ℤ) : ℝ :=
  if k = 0 then 0 else ‖k‖ ^ (-4 : ℝ)
@[simp] theorem periodicHMinusTwoWeight_zero :
    periodicHMinusTwoWeight (0 : Fin 2 → ℤ) = 0 := by
  simp [periodicHMinusTwoWeight]
theorem periodicHMinusTwoWeight_nonneg (k : Fin 2 → ℤ) :
    0 ≤ periodicHMinusTwoWeight k := by
  by_cases hk : k = 0
  · simp [periodicHMinusTwoWeight, hk]
  · simp [periodicHMinusTwoWeight, hk, Real.rpow_nonneg]
theorem summable_periodicHMinusTwoWeight :
    Summable periodicHMinusTwoWeight := by
  have h := EisensteinSeries.summable_one_div_norm_rpow
    (show (2 : ℝ) < 4 by norm_num)
  apply h.congr
  intro k
  by_cases hk : k = 0 <;> simp [periodicHMinusTwoWeight, hk]
def periodicHMinusTwoFullWeight (k : Fin 2 → ℤ) : ℝ :=
  if k = 0 then 1 else periodicHMinusTwoWeight k
@[simp] theorem periodicHMinusTwoFullWeight_zero :
    periodicHMinusTwoFullWeight (0 : Fin 2 → ℤ) = 1 := by
  simp [periodicHMinusTwoFullWeight]
theorem periodicHMinusTwoFullWeight_nonneg (k : Fin 2 → ℤ) :
    0 ≤ periodicHMinusTwoFullWeight k := by
  by_cases hk : k = 0
  · simp [periodicHMinusTwoFullWeight, hk]
  · simp [periodicHMinusTwoFullWeight, periodicHMinusTwoWeight, hk]
theorem summable_periodicHMinusTwoFullWeight :
    Summable periodicHMinusTwoFullWeight := by
  have hzero : Summable (fun k : Fin 2 → ℤ => if k = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : Fin 2 → ℤ)).subset
    intro k hk
    simp_all
  have htail : Summable periodicHMinusTwoWeight :=
    summable_periodicHMinusTwoWeight
  have hadd := hzero.add htail
  apply hadd.congr
  intro k
  by_cases hk : k = 0 <;> simp [periodicHMinusTwoFullWeight,
    periodicHMinusTwoWeight, hk]
def periodicHMinusTwoCarrier : Set ((Fin 2 → ℤ) → ℂ) :=
  {c | Summable (fun k => periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2)}
@[simp] theorem zero_mem_periodicHMinusTwoCarrier :
    (0 : (Fin 2 → ℤ) → ℂ) ∈ periodicHMinusTwoCarrier := by
  rw [periodicHMinusTwoCarrier]
  simp [periodicHMinusTwoFullWeight]
end Pphi2Clean.Continuum
