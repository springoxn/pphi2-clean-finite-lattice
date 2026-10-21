/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Free (zero interaction) specialization of Pphi2/TransferMatrix/TransferMatrix.lean.
The carrier is the continuous real time-slice configuration space, not a finite set.
-/
import Mathlib

noncomputable section
namespace Pphi2Clean.LatticeTransfer
open MeasureTheory

abbrev SpatialField (Ns : ℕ) := Fin Ns → ℝ

variable (Ns : ℕ) [NeZero Ns]

def freeSpatialAction (a mass : ℝ) (ψ : SpatialField Ns) : ℝ :=
  (1 / 2) * ∑ x : Fin Ns, a⁻¹ ^ 2 * (ψ (x + 1) - ψ x) ^ 2 +
    ∑ x : Fin Ns, (1 / 2) * mass ^ 2 * ψ x ^ 2

def timeCoupling (ψ ψ' : SpatialField Ns) : ℝ :=
  (1 / 2) * ∑ x : Fin Ns, (ψ x - ψ' x) ^ 2

def freeKernel (a mass : ℝ) (ψ ψ' : SpatialField Ns) : ℝ :=
  Real.exp (-(timeCoupling Ns ψ ψ' +
    (a / 2) * freeSpatialAction Ns a mass ψ +
    (a / 2) * freeSpatialAction Ns a mass ψ'))

theorem freeKernel_pos (a mass : ℝ) (ψ ψ' : SpatialField Ns) :
    0 < freeKernel Ns a mass ψ ψ' := Real.exp_pos _

theorem freeKernel_symmetric (a mass : ℝ) (ψ ψ' : SpatialField Ns) :
    freeKernel Ns a mass ψ ψ' = freeKernel Ns a mass ψ' ψ := by
  have heq : timeCoupling Ns ψ ψ' = timeCoupling Ns ψ' ψ := by
    unfold timeCoupling
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  unfold freeKernel
  rw [heq]
  congr 1
  ring

/-- Strict positivity of an integrable row acting on an a.e. nonnegative input
with positive-measure support. This is pointwise positivity, with no uniform
positive lower bound on the kernel. -/
theorem freeKernel_integral_pos (a mass : ℝ) (ψ : SpatialField Ns)
    (f : SpatialField Ns → ℝ)
    (hf : 0 ≤ᵐ[volume] f)
    (hsupport : 0 < volume (Function.support f))
    (hint : Integrable (fun ψ' => freeKernel Ns a mass ψ ψ' * f ψ') volume) :
    0 < ∫ ψ', freeKernel Ns a mass ψ ψ' * f ψ' := by
  have hnonneg : 0 ≤ᵐ[volume] (fun ψ' => freeKernel Ns a mass ψ ψ' * f ψ') := by
    filter_upwards [hf] with ψ' hf'
    exact mul_nonneg (freeKernel_pos Ns a mass ψ ψ').le hf'
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg hint).2
  have heq : Function.support (fun ψ' => freeKernel Ns a mass ψ ψ' * f ψ') =
      Function.support f := by
    ext ψ'
    simp only [Function.mem_support, ne_eq, mul_eq_zero,
      ne_of_gt (freeKernel_pos Ns a mass ψ ψ'), false_or]
  rwa [heq]

theorem freeKernel_row_continuous (a mass : ℝ) (ψ : SpatialField Ns) :
    Continuous (freeKernel Ns a mass ψ) := by
  unfold freeKernel timeCoupling freeSpatialAction
  fun_prop

/-- On continuous compactly supported inputs, row integrability is proved,
not assumed. The result is a concrete positive integral on real configurations. -/
theorem freeKernel_pos_on_compact_input (a mass : ℝ) (ψ : SpatialField Ns)
    (f : SpatialField Ns → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hnonneg : ∀ x, 0 ≤ f x) (x₀ : SpatialField Ns) (h₀ : f x₀ ≠ 0) :
    0 < ∫ ψ', freeKernel Ns a mass ψ ψ' * f ψ' := by
  have hcont : Continuous (fun ψ' => freeKernel Ns a mass ψ ψ' * f ψ') :=
    (freeKernel_row_continuous Ns a mass ψ).mul hf
  have hcompact : HasCompactSupport (fun ψ' => freeKernel Ns a mass ψ ψ' * f ψ') :=
    hc.mul_left
  exact integral_pos_of_integrable_nonneg_nonzero hcont
    (hcont.integrable_of_hasCompactSupport hcompact)
    (fun x => mul_nonneg (freeKernel_pos Ns a mass ψ x).le (hnonneg x))
    (mul_ne_zero (ne_of_gt (freeKernel_pos Ns a mass ψ x₀)) h₀)

end Pphi2Clean.LatticeTransfer

