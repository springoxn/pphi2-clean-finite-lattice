import AImathPPhi2Clean.FiniteRealFamilyCovarianceQuadratic
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
 theorem physicalFamilyEvalMeasure_projectedVariance_eq_covariance_quadratic
    (d N m : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Var[fun z : EuclideanSpace ℝ (Fin m) => inner ℝ t z;
      physicalFamilyEvalMeasure d N m a mass ha hmass fs] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        (∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          ω (fs i) * ω (fs j) ∂physicalGJMeasure d N a mass ha hmass) := by
  let P := physicalGJMeasure d N a mass ha hmass
  let F := physicalFamilyEvalMap d N m a mass ha hmass fs
  let S : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) → ℝ := fun ω => ∑ i : Fin m, t i * ω (fs i)
  have hF : AEMeasurable F P := by
    change AEMeasurable (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => WithLp.toLp 2 (fun j => ω (fs j))) P
    exact (physicalGJMeasure_family_hasGaussianLaw d N a mass ha hmass fs).aemeasurable
  have ht : Measurable (fun z : EuclideanSpace ℝ (Fin m) => inner ℝ t z) := by fun_prop
  have hvar_map : Var[fun z : EuclideanSpace ℝ (Fin m) => inner ℝ t z; Measure.map F P] = Var[S; P] := by
    rw [variance_map ht.aemeasurable hF]
    congr 1
    funext ω
    simp [S, F, physicalFamilyEvalMap, PiLp.inner_apply, mul_comm]
  rw [show physicalFamilyEvalMeasure d N m a mass ha hmass fs = Measure.map F P from rfl, hvar_map]
  have hSmeas : Measurable S := by
    dsimp [S]
    exact Finset.measurable_sum _ (fun i hi => by
      have hω : Measurable (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω (fs i)) := (measurable_pi_apply (fs i)).comp (comap_measurable _)
      exact hω.const_mul (t i))
  have hcoord_mem : ∀ i : Fin m, MemLp (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω (fs i)) 2 P := by
    intro i
    exact (physicalGJMeasure_eval_hasGaussianLaw d N a mass ha hmass (fs i)).memLp_two
  have hcoord_int : ∀ i : Fin m, Integrable (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => t i * ω (fs i)) P := by
    intro i
    exact ((hcoord_mem i).const_mul (t i)).integrable (by norm_num)
  have hS_mem : MemLp S 2 P := by
    dsimp [S]
    apply memLp_finsetSum
    intro i hi
    exact (hcoord_mem i).const_mul (t i)
  have hSint : ∫ ω, S ω ∂P = 0 := by
    rw [integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro i hi
      rw [integral_const_mul]
      have hz := physicalGJMeasure_family_mean_zero d N a mass ha hmass fs i
      have hzP : (∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ), ω (fs i) ∂P) = 0 := hz
      calc
        t i * (∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ), ω (fs i) ∂P) = t i * 0 := congrArg (fun x : ℝ => t i * x) hzP
        _ = 0 := mul_zero _
    · intro i hi
      exact hcoord_int i
  rw [variance_of_integral_eq_zero hSmeas.aemeasurable hSint]
  simp_rw [S, pow_two, Finset.sum_mul]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    simp_rw [Finset.mul_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      have heq : (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => t i * ω (fs i) * (t j * ω (fs j))) = (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => t i * (t j * (ω (fs i) * ω (fs j)))) := by
        funext ω
        ring
      rw [heq, integral_const_mul, integral_const_mul]
      ring
    · intro j hj
      exact ((hcoord_mem i).const_mul (t i)).integrable_mul ((hcoord_mem j).const_mul (t j))
  · intro i hi
    exact ((hcoord_mem i).const_mul (t i)).integrable_mul hS_mem

 theorem physicalFamilyEvalMeasure_projectedMean_zero
    (d N m : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    ∫ z : EuclideanSpace ℝ (Fin m), inner ℝ t z ∂physicalFamilyEvalMeasure d N m a mass ha hmass fs = 0 := by
  let P := physicalGJMeasure d N a mass ha hmass
  let F := physicalFamilyEvalMap d N m a mass ha hmass fs
  have hF : AEMeasurable F P := by
    change AEMeasurable (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => WithLp.toLp 2 (fun j => ω (fs j))) P
    exact (physicalGJMeasure_family_hasGaussianLaw d N a mass ha hmass fs).aemeasurable
  have ht : Measurable (fun z : EuclideanSpace ℝ (Fin m) => inner ℝ t z) := by fun_prop
  rw [show physicalFamilyEvalMeasure d N m a mass ha hmass fs = Measure.map F P from rfl, integral_map hF ht.aestronglyMeasurable]
  have hinner : (fun ω => inner ℝ t (F ω)) = (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ∑ i : Fin m, t i * ω (fs i)) := by
    funext ω
    simp [F, physicalFamilyEvalMap, PiLp.inner_apply, mul_comm]
  rw [hinner, integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul]
    have hz := physicalGJMeasure_family_mean_zero d N a mass ha hmass fs i
    have hzP : (∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ), ω (fs i) ∂P) = 0 := hz
    calc
      t i * (∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ), ω (fs i) ∂P) = t i * 0 := congrArg (fun x : ℝ => t i * x) hzP
      _ = 0 := mul_zero _
  · intro i hi
    exact (((physicalGJMeasure_eval_hasGaussianLaw d N a mass ha hmass (fs i)).memLp_two).const_mul (t i)).integrable (by norm_num)
end Pphi2Clean.Continuum
