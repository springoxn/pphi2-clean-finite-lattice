import AImathPPhi2Clean.PeriodicComplexFourierLift
noncomputable section
namespace Pphi2Clean.Continuum
open scoped BigOperators
def periodicHMinusTwoFullLiftTrace (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) : ℝ :=
  ∑' k, periodicHMinusTwoFullWeight k *
    periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k
def PeriodicHMinusTwoZeroModeTraceInput (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) (C : ℝ) : Prop :=
  periodicComplexFourierLiftMoment N a mass L ha hmass hperiod 0 ≤ C
theorem periodicHMinusTwoFullLiftTrace_summable
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) (C : ℝ)
    (hC : PeriodicHMinusTwoZeroModeTraceInput N a mass L ha hmass hperiod C) :
    Summable (fun k => periodicHMinusTwoFullWeight k *
      periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k) := by
  have htail := periodicHMinusTwo_complex_lift_trace_bound
    N a mass L ha hmass hL hperiod
  have hzero : Summable (fun k : Fin 2 → ℤ =>
      if k = 0 then periodicComplexFourierLiftMoment N a mass L ha hmass hperiod 0 else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : Fin 2 → ℤ)).subset
    intro k hk
    simp_all
  have hsum := hzero.add htail.1
  apply hsum.congr
  intro k
  by_cases hk : k = 0
  · simp [periodicHMinusTwoFullWeight, periodicHMinusTwoWeight, hk]
  · simp [periodicHMinusTwoFullWeight, periodicHMinusTwoWeight, hk]
theorem periodicHMinusTwoFullLiftTrace_le
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) (C : ℝ)
    (hC : PeriodicHMinusTwoZeroModeTraceInput N a mass L ha hmass hperiod C) :
    periodicHMinusTwoFullLiftTrace N a mass L ha hmass hperiod ≤
      C + (2 * (mass⁻¹ ^ 2 * L ^ 2)) * ∑' k, periodicHMinusTwoWeight k := by
  unfold periodicHMinusTwoFullLiftTrace
  have htail := periodicHMinusTwo_complex_lift_trace_bound
    N a mass L ha hmass hL hperiod
  have hzero : Summable (fun k : Fin 2 → ℤ =>
      if k = 0 then periodicComplexFourierLiftMoment N a mass L ha hmass hperiod 0 else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : Fin 2 → ℤ)).subset
    intro k hk
    simp_all
  have hdecomp : (fun k => periodicHMinusTwoFullWeight k *
      periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k) =
      (fun k => (if k = 0 then periodicComplexFourierLiftMoment N a mass L ha hmass hperiod 0 else 0) +
        periodicHMinusTwoWeight k * periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k) := by
    funext k
    by_cases hk : k = 0 <;> simp [periodicHMinusTwoFullWeight,
      periodicHMinusTwoWeight, hk]
  rw [hdecomp, hzero.tsum_add htail.1]
  have htsum_zero : ∑' k : Fin 2 → ℤ,
      (if k = 0 then periodicComplexFourierLiftMoment N a mass L ha hmass hperiod 0 else 0) =
      periodicComplexFourierLiftMoment N a mass L ha hmass hperiod 0 := by
    simp
  rw [htsum_zero]
  exact add_le_add hC htail.2
end Pphi2Clean.Continuum
