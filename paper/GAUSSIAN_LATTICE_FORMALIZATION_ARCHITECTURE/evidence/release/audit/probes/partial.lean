import AImathPPhi2Clean.PhysicalLatticeSampling
import AImathPPhi2Clean.PeriodicNegativeSobolevCarriers
import AImathPPhi2Clean.PeriodicFullHMinusTwoTraceConcrete
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
abbrev PeriodicHMinusThreeSpace :=
  {c : (Fin 2 → ℤ) → ℂ // c ∈ periodicHMinusThreeCarrier}
def PeriodicContinuumGaussianConstructionInput (L mass : ℝ) : Prop :=
  ∃ μ : Measure (PeriodicHMinusThreeSpace),
    (IsProbabilityMeasure μ) ∧
    (∀ k : Fin 2 → ℤ, ∃ v : ℝ,
      ∀ c : PeriodicHMinusThreeSpace, ‖(c : (Fin 2 → ℤ) → ℂ) k‖ ^ 2 ≤ v)
def PeriodicPhysicalLatticeWeakConvergenceInput : Prop :=
  ∀ (N : ℕ) (a mass L : ℝ),
    0 < a → 0 < mass → a * (N : ℝ) = L →
    ∃ μN : Measure (PeriodicHMinusThreeSpace),
      IsProbabilityMeasure μN
def PeriodicPhysicalFreeFieldWeakLimitInput : Prop :=
  ∀ (L mass : ℝ), 0 < L → 0 < mass →
