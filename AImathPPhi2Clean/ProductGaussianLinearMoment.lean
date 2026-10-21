import AImathPPhi2Clean.ProductGaussian
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

noncomputable section
namespace Pphi2Clean.LatticeGaussian
open MeasureTheory ProbabilityTheory

/-- A finite linear observable has an explicit second-moment bound under the
product Gaussian, using only a finite-coordinate Cauchy-Schwarz estimate. -/
theorem productGaussian_linear_second_moment_bound
    (Ns : ℕ) (σ : NNReal) (c : Fin Ns → ℝ) :
    ∫ x : SpatialField Ns, (∑ i : Fin Ns, c i * x i) ^ 2
      ∂productGaussian Ns σ ≤
      (Fintype.card (Fin Ns) : ℝ) * (∑ i : Fin Ns, c i ^ 2) * (σ : ℝ) := by
  let μ := productGaussian Ns σ
  have hcoordLp : ∀ i : Fin Ns, MemLp (fun x : SpatialField Ns => x i) 2 μ := by
    intro i
    exact (memLp_id_gaussianReal (μ := 0) (v := σ) 2).comp_measurePreserving
      (MeasureTheory.measurePreserving_eval (fun _ : Fin Ns => gaussianReal 0 σ) i)
  have hlinearLp : MemLp (fun x : SpatialField Ns => ∑ i : Fin Ns, c i * x i) 2 μ := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    exact (hcoordLp i).const_mul (c i)
  have hcoordSq : ∀ i : Fin Ns, Integrable (fun x : SpatialField Ns => x i ^ 2) μ := by
    intro i
    exact (hcoordLp i).integrable_sq
  have hsum : Integrable (fun x : SpatialField Ns =>
      ∑ i : Fin Ns, c i ^ 2 * x i ^ 2) μ := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact (hcoordSq i).const_mul (c i ^ 2)
  have hpoint : ∀ x : SpatialField Ns,
      (∑ i : Fin Ns, c i * x i) ^ 2 ≤
        (Fintype.card (Fin Ns) : ℝ) * ∑ i : Fin Ns, c i ^ 2 * x i ^ 2 := by
    intro x
    calc
      (∑ i : Fin Ns, c i * x i) ^ 2 ≤
          (Fintype.card (Fin Ns) : ℝ) * ∑ i : Fin Ns, (c i * x i) ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin Ns))) (f := fun i => c i * x i))
      _ = (Fintype.card (Fin Ns) : ℝ) * ∑ i : Fin Ns, c i ^ 2 * x i ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
  calc
    ∫ x : SpatialField Ns, (∑ i : Fin Ns, c i * x i) ^ 2 ∂μ ≤
        ∫ x : SpatialField Ns, (Fintype.card (Fin Ns) : ℝ) *
          ∑ i : Fin Ns, c i ^ 2 * x i ^ 2 ∂μ := by
      exact integral_mono_ae hlinearLp.integrable_sq (hsum.const_mul _)
        (ae_of_all _ hpoint)
    _ = (Fintype.card (Fin Ns) : ℝ) *
        ∑ i : Fin Ns, c i ^ 2 *
          (∫ x : SpatialField Ns, x i ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro i hi
        exact (hcoordSq i).const_mul (c i ^ 2)
    _ = (Fintype.card (Fin Ns) : ℝ) * (∑ i : Fin Ns, c i ^ 2) * (σ : ℝ) := by
      simp_rw [show μ = productGaussian Ns σ by rfl, productGaussian_coordinate_second_moment_eq]
      simp_rw [mul_assoc]; rw [← Finset.sum_mul]

end Pphi2Clean.LatticeGaussian
namespace Pphi2Clean.LatticeGaussian
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
 theorem productGaussian_linear_second_moment_eq (Ns : ℕ) (σ : NNReal) (c : Fin Ns → ℝ) :
    ∫ x : SpatialField Ns, (∑ i : Fin Ns, c i * x i) ^ 2
      ∂productGaussian Ns σ = (σ : ℝ) * ∑ i : Fin Ns, c i ^ 2 := by
  let μ := productGaussian Ns σ
  let F : Fin Ns → SpatialField Ns → ℝ := fun i x => x i
  let X : Fin Ns → SpatialField Ns → ℝ := fun i x => c i * x i
  have hF : iIndepFun F μ := by
    unfold F μ productGaussian
    exact iIndepFun_pi (X := fun _ y => y) (fun _ => measurable_id.aemeasurable)
  have hI : iIndepFun X μ := by
    have h := hF.comp (fun i y => c i * y) (fun i => by fun_prop)
    simpa [F, X, Function.comp_def] using h
  have hmem : ∀ i : Fin Ns, MemLp (X i) 2 μ := by
    intro i
    exact (memLp_id_gaussianReal (μ := 0) (v := σ) 2).comp_measurePreserving
      (MeasureTheory.measurePreserving_eval (fun _ : Fin Ns => gaussianReal 0 σ) i) |>.const_mul (c i)
  have hvar : ∀ i : Fin Ns, variance (X i) μ = (σ : ℝ) * c i ^ 2 := by
    intro i
    simp only [X, variance_const_mul]
    have hm : ∫ x : SpatialField Ns, x i ∂μ = 0 := by
      rw [show μ = productGaussian Ns σ by rfl]
      rw [← integral_map (μ := productGaussian Ns σ) (φ := Function.eval i)
        (measurable_pi_apply i).aemeasurable (f := fun y : ℝ => y) measurable_id.aestronglyMeasurable]
      rw [productGaussian_coordinate_map, integral_id_gaussianReal]
    have hsq : ∫ x : SpatialField Ns, (x i) ^ 2 ∂μ = (σ : ℝ) := by
      exact productGaussian_coordinate_second_moment_eq Ns σ i
    rw [variance_eq_integral (X := fun x : SpatialField Ns => x i)
      (μ := μ) ((measurable_pi_apply i).aemeasurable)]
    simp [hm, hsq]
    ring
  have hsum : variance (fun x : SpatialField Ns => ∑ i : Fin Ns, X i x) μ =
      ∑ i : Fin Ns, variance (X i) μ := by
    have hp : Set.Pairwise (↑(Finset.univ : Finset (Fin Ns)) : Set (Fin Ns))
        (fun i j => X i ⟂ᵢ[μ] X j) := by
      intro i _ j _ hij
      exact hI.indepFun hij
    have hv := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin Ns))) (X := X) (fun i hi => hmem i) hp
    rw [show (fun x : SpatialField Ns => ∑ i : Fin Ns, X i x) = ∑ i : Fin Ns, X i by funext x; simp [Finset.sum_apply]]
    exact hv
  have hmean : ∫ x : SpatialField Ns, (∑ i : Fin Ns, X i x) ∂μ = 0 := by
    rw [integral_finsetSum]
    · simp only [X, integral_const_mul]
      apply Finset.sum_eq_zero
      intro i hi
      rw [show μ = productGaussian Ns σ by rfl]
      rw [← integral_map (μ := productGaussian Ns σ) (φ := Function.eval i)
        (measurable_pi_apply i).aemeasurable (f := fun y : ℝ => y) measurable_id.aestronglyMeasurable]
      rw [productGaussian_coordinate_map, integral_id_gaussianReal, mul_zero]
    · intro i hi
      exact (hmem i).integrable (by norm_num)
  have hquad : ∫ x : SpatialField Ns, (∑ i : Fin Ns, X i x) ^ 2 ∂μ =
      variance (fun x : SpatialField Ns => ∑ i : Fin Ns, X i x) μ := by
    rw [variance_eq_integral (X := fun x : SpatialField Ns => ∑ i : Fin Ns, X i x)
      (μ := μ) ((by fun_prop : Measurable (fun x : SpatialField Ns => ∑ i : Fin Ns, X i x)).aemeasurable)]
    simp [hmean]
  calc
    ∫ x : SpatialField Ns, (∑ i : Fin Ns, c i * x i) ^ 2 ∂productGaussian Ns σ =
        ∫ x : SpatialField Ns, (∑ i : Fin Ns, X i x) ^ 2 ∂μ := by rfl
    _ = variance (fun x : SpatialField Ns => ∑ i : Fin Ns, X i x) μ := hquad
    _ = ∑ i : Fin Ns, variance (X i) μ := hsum
    _ = (σ : ℝ) * ∑ i : Fin Ns, c i ^ 2 := by simp [hvar, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

end Pphi2Clean.LatticeGaussian
