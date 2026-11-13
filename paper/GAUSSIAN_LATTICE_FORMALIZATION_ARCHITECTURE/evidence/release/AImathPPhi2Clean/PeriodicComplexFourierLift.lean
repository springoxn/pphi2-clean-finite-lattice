import AImathPPhi2Clean.PeriodicComplexFourierProbe
noncomputable section
namespace Pphi2Clean.Continuum
open Classical
open MeasureTheory ProbabilityTheory
open Pphi2Clean.UpstreamLattice
def periodicComplexFourierLift (L : ℝ) (hperiod : 0 < L)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) :
    (Fin 2 → ℤ) → ℂ :=
  fun k => periodicComplexFourierProbe L hperiod k ω
@[simp] theorem periodicComplexFourierLift_apply (L : ℝ) (hperiod : 0 < L)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ))
    (k : Fin 2 → ℤ) :
    periodicComplexFourierLift L hperiod ω k =
      periodicComplexFourierProbe L hperiod k ω := rfl
/-- The concrete negative-Sobolev carrier used by the periodic two-dimensional lift.
It is the weighted square-summable Fourier sequence subtype; the zero mode is
included through `periodicHMinusTwoFullWeight`. -/
abbrev PeriodicHMinusTwoSpace :=
  {c : (Fin 2 → ℤ) → ℂ // c ∈ periodicHMinusTwoCarrier}
/-- The raw Fourier lift before proving almost-everywhere membership in the carrier. -/
def periodicHMinusTwoLiftMap (L : ℝ) (hperiod : 0 < L)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) :
    (Fin 2 → ℤ) → ℂ := periodicComplexFourierLift L hperiod ω
/-- Explicit proof boundary for turning the raw lift into an `H⁻²`-valued map.
The first conjunct is the measurable-space input; the second is the missing
almost-everywhere carrier-membership statement. -/
def PeriodicHMinusTwoLiftInput (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) : Prop :=
  Measurable (periodicHMinusTwoLiftMap L hperiod) ∧
    ∀ᵐ ω ∂physicalGJMeasure 2 N a mass ha hmass,
      periodicHMinusTwoLiftMap L hperiod ω ∈ periodicHMinusTwoCarrier
/-- The measure-theoretic pushforward shape once a carrier-valued lift has been
constructed. The separate `AEMeasurable` hypothesis belongs to the proof input
rather than to the measure expression itself. -/
def periodicHMinusTwoLiftPushforward
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) → PeriodicHMinusTwoSpace) :
    Measure PeriodicHMinusTwoSpace :=
  Measure.map F (physicalGJMeasure 2 N a mass ha hmass)
/-- Raw infinite-dimensional lift directly on the finite lattice Gaussian source.
The source is `FiniteLatticeConfiguration`, and `latticeEmbedLift` supplies the
periodic distribution seen by continuum test functions. -/
def periodicHMinusTwoDiscreteRawLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L) :
    FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)) →
      (Fin 2 → ℤ) → ℂ :=
  fun ω => periodicHMinusTwoLiftMap L hperiod
    (latticeEmbedLift (physicalTestEval 2 N a) ω)
/-- Total carrier-valued representative. On the exceptional set where the raw
sequence is not known to be in the carrier, use the zero carrier element. -/
def periodicHMinusTwoDiscreteCarrierLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L) :
    FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)) →
      PeriodicHMinusTwoSpace :=
  fun ω => if h : periodicHMinusTwoDiscreteRawLift N a L hperiod ω ∈
      periodicHMinusTwoCarrier then
    ⟨periodicHMinusTwoDiscreteRawLift N a L hperiod ω, h⟩
  else ⟨0, zero_mem_periodicHMinusTwoCarrier⟩
/-- Minimal source-level input for the discrete carrier lift. -/
def PeriodicHMinusTwoDiscreteLiftInput (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) : Prop :=
  Measurable (periodicHMinusTwoDiscreteRawLift N a L hperiod) ∧
    ∀ᵐ ω ∂finiteCovarianceGaussianMeasure
      (numberedLatticeCovarianceGJ 2 N a mass ha hmass),
      periodicHMinusTwoDiscreteRawLift N a L hperiod ω ∈
        periodicHMinusTwoCarrier
/-- Pushforward of the finite lattice Gaussian law by the carrier-valued lift. -/
def periodicHMinusTwoDiscreteLiftMeasure (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) : Measure PeriodicHMinusTwoSpace :=
  Measure.map (periodicHMinusTwoDiscreteCarrierLift N a L hperiod)
    (finiteCovarianceGaussianMeasure
      (numberedLatticeCovarianceGJ 2 N a mass ha hmass))
@[simp] theorem periodicHMinusTwoDiscreteCarrierLift_apply_of_mem
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)))
    (hω : periodicHMinusTwoDiscreteRawLift N a L hperiod ω ∈
      periodicHMinusTwoCarrier) (k : Fin 2 → ℤ) :
    (periodicHMinusTwoDiscreteCarrierLift N a L hperiod ω).1 k =
      periodicComplexFourierLift L hperiod
        (latticeEmbedLift (physicalTestEval 2 N a) ω) k := by
  unfold periodicHMinusTwoDiscreteCarrierLift
  rw [dif_pos hω]
  rfl
@[simp] theorem periodicComplexFourierLift_norm_sq (L : ℝ) (hperiod : 0 < L)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ))
    (k : Fin 2 → ℤ) :
    ‖periodicComplexFourierLift L hperiod ω k‖ ^ 2 =
      (ω (periodicCosineTest 2 L k hperiod)) ^ 2 +
        (ω (periodicSineTest 2 L k hperiod)) ^ 2 := by
  exact periodicComplexFourierProbe_norm_sq L hperiod k ω
def periodicComplexFourierLiftMoment (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) (k : Fin 2 → ℤ) : ℝ :=
  ∫ ω, ‖periodicComplexFourierLift L hperiod ω k‖ ^ 2 ∂
    physicalGJMeasure 2 N a mass ha hmass
theorem periodicComplexFourierLiftMoment_eq (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) (k : Fin 2 → ℤ) :
    periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k =
      periodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
  unfold periodicComplexFourierLiftMoment periodicComplexFourierProbeMoment
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [periodicComplexFourierLift_apply]
theorem periodicHMinusTwo_complex_lift_trace_bound (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) :
    Summable (fun k => periodicHMinusTwoWeight k *
      periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k) ∧
      ∑' k, periodicHMinusTwoWeight k *
        periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k ≤
        (2 * (mass⁻¹ ^ 2 * L ^ 2)) *
          ∑' k, periodicHMinusTwoWeight k := by
  have h := periodicHMinusTwo_complex_probe_trace_bound N a mass L ha hmass hL hperiod
  rw [show (fun k => periodicHMinusTwoWeight k *
      periodicComplexFourierLiftMoment N a mass L ha hmass hperiod k) =
      (fun k => periodicHMinusTwoWeight k *
        periodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) by
    funext k
    rw [periodicComplexFourierLiftMoment_eq N a mass L ha hmass hL hperiod k]]
  exact h
end Pphi2Clean.Continuum
