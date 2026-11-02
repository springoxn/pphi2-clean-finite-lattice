import AImathPPhi2Clean.FiniteDimensionalGaussianConvergence
import AImathPPhi2Clean.FiniteRealFamilyCovarianceConvergence
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
theorem gaussian_charFun_tendsto_of_mean_variance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) (μ₀ : ProbabilityMeasure E)
    (hμ : ∀ n, HasGaussianLaw id (μ n : Measure E))
    (hμ₀ : HasGaussianLaw id (μ₀ : Measure E))
    (hmean : ∀ t : E, Filter.Tendsto
      (fun n => ∫ x : E, inner ℝ t x ∂(μ n)) Filter.atTop
        (nhds (∫ x : E, inner ℝ t x ∂μ₀)))
    (hvar : ∀ t : E, Filter.Tendsto
      (fun n => Var[fun x : E => inner ℝ t x; μ n]) Filter.atTop
        (nhds (Var[fun x : E => inner ℝ t x; μ₀]))) :
    ∀ t : E, Filter.Tendsto
      (fun n => charFun (μ n) t) Filter.atTop
        (nhds (charFun μ₀ t)) := by
  intro t
  have harg : Filter.Tendsto
      (fun n =>
        ((∫ x : E, inner ℝ t x ∂(μ n) : ℝ) : ℂ) * Complex.I -
          (Var[fun x : E => inner ℝ t x; μ n] : ℂ) / 2)
      Filter.atTop
      (nhds
        (((∫ x : E, inner ℝ t x ∂μ₀ : ℝ) : ℂ) * Complex.I -
          (Var[fun x : E => inner ℝ t x; μ₀] : ℂ) / 2)) := by
    have hmean' := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hmean t))
    have hvar' := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hvar t))
    exact (hmean'.mul_const Complex.I).sub (hvar'.div_const 2)
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp harg
  have hformula : ∀ n, charFun (μ n) t =
      Complex.exp (((∫ x : E, inner ℝ t x ∂(μ n) : ℝ) : ℂ) * Complex.I -
        (Var[fun x : E => inner ℝ t x; μ n] : ℂ) / 2) := by
    intro n
    simpa only [Measure.map_id, id_eq] using (hμ n).charFun_map_eq t
  have hformula₀ : charFun μ₀ t =
      Complex.exp (((∫ x : E, inner ℝ t x ∂μ₀ : ℝ) : ℂ) * Complex.I -
        (Var[fun x : E => inner ℝ t x; μ₀] : ℂ) / 2) := by
    simpa only [Measure.map_id, id_eq] using hμ₀.charFun_map_eq t
  rw [show (fun n => charFun (μ n) t) =
      (fun n => Complex.exp (((∫ x : E, inner ℝ t x ∂(μ n) : ℝ) : ℂ) * Complex.I -
        (Var[fun x : E => inner ℝ t x; μ n] : ℂ) / 2)) from funext (fun n => hformula n),
    hformula₀]
  exact hexp
theorem finiteGaussian_weak_tendsto_of_mean_variance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) (μ₀ : ProbabilityMeasure E)
    (hμ : ∀ n, HasGaussianLaw id (μ n : Measure E))
    (hμ₀ : HasGaussianLaw id (μ₀ : Measure E))
    (hmean : ∀ t : E, Filter.Tendsto
      (fun n => ∫ x : E, inner ℝ t x ∂(μ n)) Filter.atTop
        (nhds (∫ x : E, inner ℝ t x ∂μ₀)))
    (hvar : ∀ t : E, Filter.Tendsto
      (fun n => Var[fun x : E => inner ℝ t x; μ n]) Filter.atTop
        (nhds (Var[fun x : E => inner ℝ t x; μ₀]))) :
    Filter.Tendsto μ Filter.atTop (nhds μ₀) := by
  apply finiteDimensional_weak_tendsto_of_charFun μ μ₀
  exact gaussian_charFun_tendsto_of_mean_variance μ μ₀ hμ hμ₀ hmean hvar
end Pphi2Clean.Continuum
