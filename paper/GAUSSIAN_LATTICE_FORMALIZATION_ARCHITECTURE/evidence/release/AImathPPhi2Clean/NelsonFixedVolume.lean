import AImathPPhi2Clean.NelsonBridge

noncomputable section

namespace Pphi2Clean.Nelson

open MeasureTheory

/-- Fixed physical-volume Nelson interface.

The uniformity is only over pairs `(N, a)` satisfying `N * a = L`.
The tail estimate and the total-mass bound are explicit hypotheses; this
interface does not assert either of them for the P(phi)_2 lattice model. -/
theorem fixed_volume_nelson_bound
    {α : Type*} [MeasurableSpace α]
    (L : ℝ) (μ : ℕ → ℝ → Measure α) (V : ℕ → ℝ → α → ℝ) (V_S E_R : ℕ → ℝ → ℝ → α → ℝ)
    (ψ : ℝ → ENNReal) (Kμ R : ENNReal)
    (hKμ : 0 < Kμ) (hR : 0 ≤ R)
    (hSFinite : ∀ (N : ℕ) (a : ℝ), SFinite (μ N a))
    (hμ : ∀ (N : ℕ) [NeZero N] (a : ℝ), 0 < a → (N : ℝ) * a = L → μ N a Set.univ ≤ Kμ)
    (hψ : ∫⁻ t in Set.Ioi (0 : ℝ),
        ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) ≤ R)
    (hV : ∀ (N : ℕ) [NeZero N] (a : ℝ), Measurable (V N a))
    (hdecomp : ∀ (N : ℕ) [NeZero N] (a M : ℝ) (ω : α),
      V N a ω = V_S N a M ω + E_R N a M ω)
    (hsmooth : ∀ (N : ℕ) [NeZero N] (a M : ℝ) (ω : α),
      -(M / 2) ≤ V_S N a M ω)
    (htail : ∀ (N : ℕ) [NeZero N] (a M : ℝ), 0 < M →
      μ N a {ω | E_R N a M ω ≤ -(M / 2)} ≤ ψ M) :
    ∃ K : ENNReal, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ), 0 < a → (N : ℝ) * a = L →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-V N a ω) ^ 2) ∂(μ N a) ≤ K := by
  refine ⟨Kμ + R, ?_, ?_⟩
  · exact lt_of_lt_of_le hKμ (le_add_of_nonneg_right hR)
  · intro N _ a ha hvol
    letI : SFinite (μ N a) := hSFinite N a
    have hbridge := expSqNeg_lintegral_le_of_dynamical_cutoff
      (μ N a) (V N a) (hV N a) (V_S N a) (E_R N a)
      (fun M ω => hdecomp N a M ω)
      (fun M ω => hsmooth N a M ω) ψ
      (fun M hM => htail N a M hM)
    calc
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-V N a ω) ^ 2) ∂(μ N a)
          ≤ μ N a Set.univ +
            ∫⁻ t in Set.Ioi (0 : ℝ),
              ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) := hbridge
      _ ≤ Kμ + R := add_le_add (hμ N a ha hvol) hψ

end Pphi2Clean.Nelson
