import AImathPPhi2Clean.FiniteRealFamilyCharacteristicFunction
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
theorem finiteGaussian_weak_tendsto_of_covariance_entries
    {m : ℕ} (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
    (μ₀ : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
    (hμ : ∀ n, HasGaussianLaw id (μ n : Measure (EuclideanSpace ℝ (Fin m))))
    (hμ₀ : HasGaussianLaw id (μ₀ : Measure (EuclideanSpace ℝ (Fin m))))
    (hmean : ∀ t : EuclideanSpace ℝ (Fin m), Filter.Tendsto
      (fun n => ∫ x, inner ℝ t x ∂(μ n)) Filter.atTop
        (nhds (∫ x, inner ℝ t x ∂μ₀)))
    (C : Fin m → Fin m → ℝ)
    (Cn : ℕ → Fin m → Fin m → ℝ)
    (hcov : ∀ i j, Filter.Tendsto (fun n => Cn n i j) Filter.atTop
      (nhds (C i j)))
    (hquad : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin m)),
      Var[fun x => inner ℝ t x; (μ n : Measure (EuclideanSpace ℝ (Fin m)))] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j * Cn n i j)
    (hquad₀ : ∀ (t : EuclideanSpace ℝ (Fin m)),
      Var[fun x => inner ℝ t x; (μ₀ : Measure (EuclideanSpace ℝ (Fin m)))] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j * C i j) :
    Filter.Tendsto μ Filter.atTop (nhds μ₀) := by
  apply finiteGaussian_weak_tendsto_of_mean_variance μ μ₀ hμ hμ₀ hmean
  intro t
  have hsum : Filter.Tendsto
      (fun n => ∑ i : Fin m, ∑ j : Fin m, t i * t j * Cn n i j)
      Filter.atTop
      (nhds (∑ i : Fin m, ∑ j : Fin m, t i * t j * C i j)) := by
    apply tendsto_finset_sum (Finset.univ : Finset (Fin m))
    intro i hi
    apply tendsto_finset_sum (Finset.univ : Finset (Fin m))
    intro j hj
    simpa [mul_assoc] using (hcov i j).const_mul (t i * t j)
  rw [show (fun n => Var[fun x => inner ℝ t x;
      (μ n : Measure (EuclideanSpace ℝ (Fin m)))]) =
      (fun n => ∑ i : Fin m, ∑ j : Fin m, t i * t j * Cn n i j) from
        funext (fun n => hquad n t), hquad₀ t]
  exact hsum
end Pphi2Clean.Continuum
