import AImathPPhi2Clean.DimensionFreeWeightSummability
noncomputable section
namespace Pphi2Clean.DimensionFreeProbe

theorem finite_frequency_ball (d R : ℕ) :
    Set.Finite {k : Fin d → ℤ | ‖k‖ ≤ (R : ℝ)} := by
  classical
  let t : Fin d → Set ℤ := fun _ => Set.Icc (-(R : ℤ)) (R : ℤ)
  have ht : {k : Fin d → ℤ | ∀ i : Fin d, k i ∈ t i}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  apply ht.subset
  intro k hk
  change ∀ i : Fin d, k i ∈ t i
  intro i
  have hcoord : ‖(k i : ℝ)‖ ≤ (R : ℝ) := (norm_le_pi_norm k i).trans hk
  have habsReal : |(k i : ℝ)| ≤ (R : ℝ) := by simpa [Real.norm_eq_abs] using hcoord
  have habsCast : ((|k i| : ℤ) : ℝ) ≤ (R : ℝ) := by simpa [Int.cast_abs] using habsReal
  have habs : |k i| ≤ (R : ℤ) := by exact_mod_cast habsCast
  exact Set.mem_Icc.mpr (abs_le.mp habs)

#print axioms finite_frequency_ball
end Pphi2Clean.DimensionFreeProbe
