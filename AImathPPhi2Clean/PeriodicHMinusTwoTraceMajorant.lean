import AImathPPhi2Clean.PeriodicHMinusTwoWeight
noncomputable section
namespace Pphi2Clean.Continuum
open scoped BigOperators
theorem periodicHMinusTwo_weighted_series_bound
    {b : (Fin 2 → ℤ) → ℝ} {C : ℝ}
    (hb_nonneg : ∀ k, 0 ≤ b k) (hb_bound : ∀ k, b k ≤ C)
    (hC : 0 ≤ C) :
    Summable (fun k => periodicHMinusTwoWeight k * b k) ∧
      ∑' k, periodicHMinusTwoWeight k * b k ≤
        C * ∑' k, periodicHMinusTwoWeight k := by
  have hw := summable_periodicHMinusTwoWeight
  have hmajor : Summable (fun k => C * periodicHMinusTwoWeight k) :=
    hw.mul_left C
  have hnonneg : ∀ k, 0 ≤ periodicHMinusTwoWeight k * b k := by
    intro k
    exact mul_nonneg (periodicHMinusTwoWeight_nonneg k) (hb_nonneg k)
  have hle : ∀ k, periodicHMinusTwoWeight k * b k ≤
      C * periodicHMinusTwoWeight k := by
    intro k
    calc
      periodicHMinusTwoWeight k * b k ≤ periodicHMinusTwoWeight k * C := by
        exact mul_le_mul_of_nonneg_left (hb_bound k)
          (periodicHMinusTwoWeight_nonneg k)
      _ = C * periodicHMinusTwoWeight k := by ring
  have hs : Summable (fun k => periodicHMinusTwoWeight k * b k) :=
    hmajor.of_nonneg_of_le hnonneg hle
  refine ⟨hs, ?_⟩
  have hsum := hs.tsum_le_tsum hle hmajor
  simpa [tsum_mul_left] using hsum
end Pphi2Clean.Continuum
