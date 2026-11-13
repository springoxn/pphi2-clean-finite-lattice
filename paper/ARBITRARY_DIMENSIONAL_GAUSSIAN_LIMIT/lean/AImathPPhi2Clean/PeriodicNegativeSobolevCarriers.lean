import AImathPPhi2Clean.PeriodicHMinusTwoWeight
noncomputable section
namespace Pphi2Clean.Continuum
open scoped BigOperators
def periodicHMinusThreeWeight (k : Fin 2 → ℤ) : ℝ :=
  if k = 0 then 1 else ‖k‖ ^ (-6 : ℝ)
@[simp] theorem periodicHMinusThreeWeight_zero :
    periodicHMinusThreeWeight (0 : Fin 2 → ℤ) = 1 := by
  simp [periodicHMinusThreeWeight]
theorem periodicHMinusThreeWeight_nonneg (k : Fin 2 → ℤ) :
    0 ≤ periodicHMinusThreeWeight k := by
  by_cases hk : k = 0
  · simp [periodicHMinusThreeWeight, hk]
  · simp [periodicHMinusThreeWeight, hk, Real.rpow_nonneg]
theorem summable_periodicHMinusThreeWeight :
    Summable periodicHMinusThreeWeight := by
  have hzero : Summable (fun k : Fin 2 → ℤ => if k = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : Fin 2 → ℤ)).subset
    intro k hk
    simp_all
  have htail : Summable (fun k : Fin 2 → ℤ =>
      if k = 0 then 0 else ‖k‖ ^ (-6 : ℝ)) := by
    have h := EisensteinSeries.summable_one_div_norm_rpow
      (show (2 : ℝ) < 6 by norm_num)
    apply h.congr
    intro k
    by_cases hk : k = 0 <;> simp [hk]
  have hadd := hzero.add htail
  apply hadd.congr
  intro k
  by_cases hk : k = 0 <;> simp [periodicHMinusThreeWeight, hk]
def periodicHMinusThreeCarrier : Set ((Fin 2 → ℤ) → ℂ) :=
  {c | Summable (fun k => periodicHMinusThreeWeight k * ‖c k‖ ^ 2)}
@[simp] theorem zero_mem_periodicHMinusThreeCarrier :
    (0 : (Fin 2 → ℤ) → ℂ) ∈ periodicHMinusThreeCarrier := by
  rw [periodicHMinusThreeCarrier]
  simp [periodicHMinusThreeWeight]
def PeriodicHMinusTwoToHMinusThreeCarrierInclusionInput : Prop :=
  ∀ c : (Fin 2 → ℤ) → ℂ, c ∈ periodicHMinusTwoCarrier →
    c ∈ periodicHMinusThreeCarrier
end Pphi2Clean.Continuum
