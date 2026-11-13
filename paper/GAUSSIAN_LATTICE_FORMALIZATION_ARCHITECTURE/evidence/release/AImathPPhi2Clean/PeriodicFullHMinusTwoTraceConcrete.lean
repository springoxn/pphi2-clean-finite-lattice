import AImathPPhi2Clean.PeriodicZeroModeTrace
noncomputable section
namespace Pphi2Clean.Continuum
theorem periodicHMinusTwoFullLiftTrace_concrete_summable
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    Summable (fun k => periodicHMinusTwoFullWeight k *
      periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k) := by
  apply periodicHMinusTwoFullLiftTrace_summable N a mass L ha hmass hL hperiod
    (mass⁻¹ ^ 2 * L ^ 2)
  exact periodicComplexFourierLiftMoment_zero_le N a mass L ha hmass hL hperiod
theorem periodicHMinusTwoFullLiftTrace_concrete_le
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    periodicHMinusTwoFullLiftTrace N a mass L ha hmass hperiod ≤
      mass⁻¹ ^ 2 * L ^ 2 +
        (2 * (mass⁻¹ ^ 2 * L ^ 2)) * ∑' k, periodicHMinusTwoWeight k := by
  apply periodicHMinusTwoFullLiftTrace_le N a mass L ha hmass hL hperiod
    (mass⁻¹ ^ 2 * L ^ 2)
  exact periodicComplexFourierLiftMoment_zero_le N a mass L ha hmass hL hperiod
end Pphi2Clean.Continuum
