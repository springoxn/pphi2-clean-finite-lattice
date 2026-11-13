import AImathPPhi2Clean.FiniteRealFamilyMeasure
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice
theorem physicalFamilyEvalMeasure_fixedVolume_covariance_entry_tendsto
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ →
      BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ
          (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField
              (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField
              (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g))) :
    ∀ i j, Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        ∫ z : EuclideanSpace ℝ (Fin m), z i * z j ∂
          physicalFamilyEvalMeasure d N m (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop (nhds (C (fs i) (fs j))) := by
  intro i j
  have hcov := physicalGJMeasure_fixedVolume_covariance_tendsto_of_inner_tendsto
    d L mass hL hmass C hinner (fs i) (fs j)
  have heq : (fun n : ℕ =>
      let N := n + 1
      letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
      ∫ z : EuclideanSpace ℝ (Fin m), z i * z j ∂
        physicalFamilyEvalMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs) =
    (fun n : ℕ =>
      let N := n + 1
      letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
      ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
        ω (fs i) * ω (fs j) ∂
          physicalGJMeasure d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass) := by
    funext n
    let N := n + 1
    letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    exact physicalFamilyEvalMeasure_covariance_entry d N m
      (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs i j
  rw [heq]
  exact hcov
end Pphi2Clean.Continuum
