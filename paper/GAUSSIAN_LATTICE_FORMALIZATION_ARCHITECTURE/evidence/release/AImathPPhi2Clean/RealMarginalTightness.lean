import AImathPPhi2Clean.TightnessChebyshev

noncomputable section

namespace Pphi2Clean.Continuum
open MeasureTheory

/-- Uniform second moments give compact containment on the real line.
This applies to scalar marginal laws; it is not tightness on a distribution space. -/
theorem real_compact_containment_of_second_moment
    {ι : Type*} (μ : ι → Measure ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h_int : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μ i))
    (h_moment : ∀ i, ∫ x : ℝ, x ^ 2 ∂(μ i) ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set ℝ, IsCompact K ∧ ∀ i, μ i Kᶜ ≤ ENNReal.ofReal ε := by
  let R : ℝ := Real.sqrt (C / ε + 1)
  have hq : 0 < C / ε + 1 := by positivity
  have hR : 0 < R := Real.sqrt_pos.2 hq
  have hsq : R ^ 2 = C / ε + 1 := Real.sq_sqrt hq.le
  have hratio : C / R ^ 2 ≤ ε := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    rw [hsq]
    have heq : ε * (C / ε) = C := by field_simp
    nlinarith
  refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
  intro i
  calc
    μ i (Set.Icc (-R) R)ᶜ ≤ μ i {x : ℝ | R ≤ |x|} := by
      apply measure_mono
      intro x hx
      have hx' : ¬ (-R ≤ x ∧ x ≤ R) := hx
      change R ≤ |x|
      rcases not_and_or.mp hx' with h | h
      · exact le_trans (by linarith) (neg_le_abs x)
      · exact le_trans (by linarith) (le_abs_self x)
    _ ≤ ENNReal.ofReal (C / R ^ 2) :=
      uniform_second_moment_tail_bound μ (fun x => x) R C hR h_int h_moment i
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_mono hratio

end Pphi2Clean.Continuum
