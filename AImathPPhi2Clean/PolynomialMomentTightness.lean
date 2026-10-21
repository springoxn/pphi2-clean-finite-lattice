/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from GaussianField/Tightness.lean: polynomial basis moments,
coordinate-box tail summation, and choice of radius. Concrete nuclear-space
coefficient estimates remain explicit inputs.
-/
import AImathPPhi2Clean.PolynomialWeakDualBox

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory

/-- Polynomially growing moments paired with one extra power in the box radius
leave an inverse-square, summable tail budget. -/
theorem polynomial_tail_budget (B D : ℝ) (s : ℕ) (hD : 0 < D) :
    (∑' n : ℕ, ENNReal.ofReal
      (B * (1 + (n : ℝ)) ^ (2 * s) / (D * (1 + (n : ℝ)) ^ (s + 1)) ^ 2)) =
      ENNReal.ofReal ((B / D ^ 2) * ∑' n : ℕ, 1 / (1 + (n : ℝ)) ^ 2) := by
  have heq : ∀ n : ℕ,
      B * (1 + (n : ℝ)) ^ (2 * s) / (D * (1 + (n : ℝ)) ^ (s + 1)) ^ 2 =
      B / D ^ 2 * (1 / (1 + (n : ℝ)) ^ 2) := by
    intro n
    rw [mul_pow, pow_add, mul_pow, ← pow_mul, Nat.mul_comm s 2]
    field_simp
  simp_rw [heq]
  by_cases hB : 0 ≤ B
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (inverseSquare_summable.mul_left (B / D ^ 2)), tsum_mul_left]
  · have hneg : B < 0 := lt_of_not_ge hB
    have hterm : ∀ n : ℕ, B / D ^ 2 * (1 / (1 + (n : ℝ)) ^ 2) ≤ 0 := by
      intro n
      exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg D))
        (by positivity)
    simp_rw [ENNReal.ofReal_eq_zero.mpr (hterm _)]
    rw [tsum_zero, ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg D)) (tsum_nonneg (fun n => by positivity))) ]

/-- Uniform polynomial second-moment bounds yield compact containment in the
weak dual, provided basis expansion and the requisite coefficient decay hold.
The finite radius is constructed for each positive error tolerance. -/
theorem weakDual_compact_containment_of_polynomial_moments
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [MeasurableSpace (WeakDual ℝ E)]
    {ι : Type*} (μ : ι → Measure (WeakDual ℝ E))
    (basis : ℕ → E) (coeff : ℕ → E →ₗ[ℝ] ℝ)
    (s : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (p : Seminorm ℝ E) (hp : Continuous p)
    (hdecay : ∀ f n, |coeff n f| * (1 + (n : ℝ)) ^ ((s + 1) + 2) ≤ p f)
    (hexpand : ∀ (ω : WeakDual ℝ E) f,
      ω f = ∑' n, coeff n f * ω (basis n))
    (h_int : ∀ n i, Integrable (fun ω => ω (basis n) ^ 2) (μ i))
    (h_moment : ∀ n i, ∫ ω, ω (basis n) ^ 2 ∂(μ i) ≤ B * (1 + (n : ℝ)) ^ (2 * s))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (WeakDual ℝ E), IsCompact K ∧ ∀ i, μ i Kᶜ ≤ ENNReal.ofReal ε := by
  let S : ℝ := ∑' n : ℕ, 1 / (1 + (n : ℝ)) ^ 2
  have hS : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  let D : ℝ := Real.sqrt (B * S / ε + 1)
  have hq : 0 < B * S / ε + 1 := by positivity
  have hD : 0 < D := Real.sqrt_pos.2 hq
  have hsq : D ^ 2 = B * S / ε + 1 := Real.sq_sqrt hq.le
  have hbudget : (B / D ^ 2) * S ≤ ε := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hD)).2
    rw [hsq]
    have heq : ε * (B * S / ε) = B * S := by field_simp
    nlinarith
  let R : ℕ → ℝ := fun n => D * (1 + (n : ℝ)) ^ (s + 1)
  refine ⟨observableBox (fun n ω => ω (basis n)) R,
    polynomial_weakDual_box_isCompact basis coeff (s + 1) D hD.le p hp hdecay hexpand, ?_⟩
  intro i
  calc
    μ i (observableBox (fun n ω => ω (basis n)) R)ᶜ ≤
        ∑' n : ℕ, ENNReal.ofReal
          (B * (1 + (n : ℝ)) ^ (2 * s) / R n ^ 2) :=
      observableBox_compl_le μ (fun n ω => ω (basis n)) R
        (fun n => B * (1 + (n : ℝ)) ^ (2 * s)) (fun n => by dsimp [R]; positivity) h_int h_moment i
    _ = ENNReal.ofReal ((B / D ^ 2) * S) := polynomial_tail_budget B D s hD
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_mono hbudget

end Pphi2Clean.Continuum
