import AImathPPhi2Clean.PhysicalLatticeSampling
open MeasureTheory ProbabilityTheory
abbrev X := {c : ℕ → ℂ // True}
def Q : Prop := ∃ μ : Measure X, IsProbabilityMeasure μ ∧ (∀ k : ℕ, ∃ v : ℝ, ∀ᵐ c : X ∂μ, ‖(c : ℕ → ℂ) k‖ ^ 2 ≤ v)
