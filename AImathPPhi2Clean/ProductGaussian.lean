import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace Pphi2Clean.LatticeGaussian
open MeasureTheory ProbabilityTheory

abbrev SpatialField (Ns : ℕ) := Fin Ns → ℝ

def productGaussian (Ns : ℕ) (σ : NNReal) : Measure (SpatialField Ns) :=
  Measure.pi (fun _ : Fin Ns => gaussianReal 0 (σ : NNReal))

instance productGaussian_isProbability (Ns : ℕ) (σ : NNReal) :
    IsProbabilityMeasure (productGaussian Ns σ) := by
  unfold productGaussian
  infer_instance

theorem productGaussian_coordinate_map (Ns : ℕ) (σ : NNReal) (i : Fin Ns) :
    (productGaussian Ns σ).map (Function.eval i) = gaussianReal 0 (σ : NNReal) := by
  unfold productGaussian
  rw [Measure.pi_map_eval]
  simp

/-- The coordinate marginal of the finite product Gaussian is the declared
one-dimensional Gaussian. The second-moment identity is left in marginal form
so the finite-dimensional covariance consumer can use it without hidden axioms. -/
theorem productGaussian_coordinate_second_moment
    (Ns : ℕ) (σ : NNReal) (i : Fin Ns) :
    ∫ x : SpatialField Ns, (x i) ^ 2 ∂productGaussian Ns σ =
      ∫ y : ℝ, y ^ 2 ∂gaussianReal 0 (σ : NNReal) := by
  have h := integral_map (μ := productGaussian Ns σ) (measurable_pi_apply i).aemeasurable (f := fun y : ℝ => y ^ 2) (by fun_prop)
  rw [productGaussian_coordinate_map] at h
  exact h.symm

theorem gaussianReal_integral_sq_zero (σ : NNReal) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 σ = (σ : ℝ) := by
  have hmean : (∫ x : ℝ, x ∂gaussianReal 0 σ) = 0 := integral_id_gaussianReal
  have hvar : Var[id; gaussianReal 0 σ] = (σ : ℝ) := variance_id_gaussianReal
  calc
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 σ =
        ∫ x : ℝ, (id x - ∫ y : ℝ, id y ∂gaussianReal 0 σ) ^ 2 ∂gaussianReal 0 σ := by simp [hmean]
    _ = Var[id; gaussianReal 0 σ] := (variance_eq_integral (measurable_id'.aemeasurable)).symm
    _ = (σ : ℝ) := hvar

theorem productGaussian_coordinate_second_moment_eq
    (Ns : ℕ) (σ : NNReal) (i : Fin Ns) :
    ∫ x : SpatialField Ns, (x i) ^ 2 ∂productGaussian Ns σ = (σ : ℝ) := by
  rw [productGaussian_coordinate_second_moment, gaussianReal_integral_sq_zero]

end Pphi2Clean.LatticeGaussian


