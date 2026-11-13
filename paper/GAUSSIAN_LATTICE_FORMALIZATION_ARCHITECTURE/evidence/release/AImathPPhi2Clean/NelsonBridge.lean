import AImathPPhi2Clean.NelsonLayerCake

noncomputable section

namespace Pphi2Clean.Nelson

open MeasureTheory

/-- Smooth/rough tail transfer used by the dynamical-cutoff argument. -/
theorem measure_le_neg_of_smooth_rough_split
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (V : α → ℝ)
    (V_S E_R : ℝ → α → ℝ)
    (hdecomp : ∀ M ω, V ω = V_S M ω + E_R M ω)
    (hsmooth : ∀ M ω, -(M / 2) ≤ V_S M ω)
    (ψ : ℝ → ENNReal)
    (htail : ∀ M, 0 < M → μ {ω | E_R M ω ≤ -(M / 2)} ≤ ψ M)
    (M : ℝ) (hM : 0 < M) :
    μ {ω | V ω ≤ -M} ≤ ψ M := by
  refine le_trans (measure_mono ?_) (htail M hM)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have h_eq := hdecomp M ω
  have h_smooth := hsmooth M ω
  linarith

/-- Abstract Nelson bridge: a measurable smooth/rough decomposition and a
rough tail bound imply the Boltzmann L² layer-cake estimate. -/
theorem expSqNeg_lintegral_le_of_dynamical_cutoff
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (V : α → ℝ) (hV : Measurable V)
    (V_S E_R : ℝ → α → ℝ)
    (hdecomp : ∀ M ω, V ω = V_S M ω + E_R M ω)
    (hsmooth : ∀ M ω, -(M / 2) ≤ V_S M ω)
    (ψ : ℝ → ENNReal)
    (htail : ∀ M, 0 < M → μ {ω | E_R M ω ≤ -(M / 2)} ≤ ψ M) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-V ω) ^ 2) ∂μ ≤
      μ Set.univ +
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) := by
  refine Pphi2Clean.Nelson.LayerCake.lintegral_expSq_neg_le_of_tail μ V hV ψ ?_
  intro t ht
  exact measure_le_neg_of_smooth_rough_split μ V V_S E_R hdecomp hsmooth ψ htail t ht

end Pphi2Clean.Nelson
