import AImathPPhi2Clean.PeriodicFS4DCompactEmbedding

noncomputable section

namespace Pphi2Clean.Continuum

def fs4HminusFourRealCarrier : Set FS4HminusFourCompletion :=
  {x | ∀ k : FS4Index, x (fun i => -k i) = star (x k)}

theorem fs4HminusFourRealCarrier_closed : IsClosed fs4HminusFourRealCarrier := by
  rw [show fs4HminusFourRealCarrier = ⋂ k : FS4Index,
      {x : FS4HminusFourCompletion | x (fun i => -k i) = star (x k)} by
    ext x
    simp [fs4HminusFourRealCarrier]]
  apply isClosed_iInter
  intro k
  exact isClosed_eq
    (fs4HminusFour_coordinate_continuous (fun i => -k i))
    ((fs4HminusFour_coordinate_continuous k).star)

theorem fs4HminusFour_zero_mem_realCarrier :
    (0 : FS4HminusFourCompletion) ∈ fs4HminusFourRealCarrier := by
  intro k
  simp

theorem isCompact_closure_fs4HminusThreeRealSlice (B : ℝ) (hB : 0 ≤ B) :
    IsCompact (closure
      (fs4HminusThreeBallInHminusFour B ∩ fs4HminusFourRealCarrier)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  constructor
  · have hcl : TotallyBounded
        (closure (fs4HminusThreeBallInHminusFour B)) :=
      (fs4HminusThreeBall_totallyBounded B hB).closure
    rw [Metric.totallyBounded_iff] at hcl ⊢
    intro ε hε
    obtain ⟨centers, hfinite, hcover⟩ := hcl ε hε
    refine ⟨centers, hfinite, ?_⟩
    have hsub :
        fs4HminusThreeBallInHminusFour B ∩ fs4HminusFourRealCarrier ⊆
          fs4HminusThreeBallInHminusFour B := fun _ hx => hx.1
    intro x hx
    exact hcover (closure_mono hsub hx)
  · exact isClosed_closure.isComplete

end Pphi2Clean.Continuum
