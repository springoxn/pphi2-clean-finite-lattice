import Mathlib

noncomputable section

namespace Pphi2Clean.OS
open MeasureTheory

/-- Abstract scalar reflection positivity for a measure, reflection map, and
class of test functions. -/
def IsRP {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Θ : X → X) (S : Set (X → ℝ)) : Prop :=
  ∀ F ∈ S, ∫ x, F x * F (Θ x) ∂μ ≥ 0

/-- Reflection positivity is closed under weak convergence against bounded
continuous test products. -/
theorem rp_closed_under_weak_limit
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (Θ : X → X) (hΘ : Continuous Θ)
    (S : Set (X → ℝ))
    (hS_bdd : ∀ F ∈ S, ∃ C, ∀ x, |F x| ≤ C)
    (hS_cont : ∀ F ∈ S, Continuous F)
    (μ : ℕ → Measure X) (μ_lim : Measure X)
    (h_rp : ∀ n, IsRP (μ n) Θ S)
    (h_weak : ∀ (g : X → ℝ), Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Filter.Tendsto (fun n => ∫ x, g x ∂(μ n)) Filter.atTop
        (nhds (∫ x, g x ∂μ_lim))) :
    IsRP μ_lim Θ S := by
  intro F hF
  have hF_cont := hS_cont F hF
  obtain ⟨C, hC⟩ := hS_bdd F hF
  have hg_cont : Continuous (fun x => F x * F (Θ x)) :=
    hF_cont.mul (hF_cont.comp hΘ)
  have hg_bdd : ∃ C', ∀ x, |(fun x => F x * F (Θ x)) x| ≤ C' :=
    ⟨C * C, fun x => by
      simp only
      rw [abs_mul]
      nlinarith [hC x, hC (Θ x), abs_nonneg (F x), abs_nonneg (F (Θ x))]⟩
  have h_tend := h_weak _ hg_cont hg_bdd
  exact ge_of_tendsto h_tend (.of_forall (fun n => h_rp n F hF))

end Pphi2Clean.OS
