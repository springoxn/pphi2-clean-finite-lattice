import AImathPPhi2Clean.CoordinateTightness

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory

/-- Coordinatewise uniform second moments give compact containment on real
sequences with the product topology. The geometric error budget is constructed
here rather than assumed. No independence or probability instance is needed. -/
theorem sequence_compact_containment_of_second_moments
    {ι : Type*} (μ : ι → Measure (ℕ → ℝ)) (C : ℕ → ℝ)
    (hC : ∀ n, 0 ≤ C n)
    (h_int : ∀ n i, Integrable (fun x => x n ^ 2) (μ i))
    (h_moment : ∀ n i, ∫ x, x n ^ 2 ∂(μ i) ≤ C n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (ℕ → ℝ), IsCompact K ∧ ∀ i, μ i Kᶜ ≤ ENNReal.ofReal ε := by
  let δ : ℕ → ℝ := fun n => ε / 2 / 2 ^ n
  have hδ : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
  let R : ℕ → ℝ := fun n => Real.sqrt (C n / δ n + 1)
  have hq : ∀ n, 0 < C n / δ n + 1 := fun n => by
    have := hC n
    have := hδ n
    positivity
  have hR : ∀ n, 0 < R n := fun n => Real.sqrt_pos.2 (hq n)
  have hratio : ∀ n, C n / R n ^ 2 ≤ δ n := by
    intro n
    apply (div_le_iff₀ (sq_pos_of_pos (hR n))).2
    have hsq : R n ^ 2 = C n / δ n + 1 := Real.sq_sqrt (hq n).le
    rw [hsq]
    have heq : δ n * (C n / δ n) = C n := by
      field_simp [ne_of_gt (hδ n)]
    nlinarith [hδ n]
  apply sequence_compact_containment_of_tail_budget μ R C hR h_int h_moment
  calc
    (∑' n, ENNReal.ofReal (C n / R n ^ 2)) ≤ ∑' n, ENNReal.ofReal (δ n) :=
      ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_mono (hratio n))
    _ = ENNReal.ofReal (∑' n, δ n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => (hδ n).le)
        (summable_geometric_two' ε)).symm
    _ = ENNReal.ofReal ε := by rw [tsum_geometric_two' ε]

end Pphi2Clean.Continuum
