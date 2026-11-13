import AImathPPhi2Clean.RealLatticeSpectralCovariance
import AImathPPhi2Clean.ProductGaussianLinearMoment
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
noncomputable def finiteFieldConfiguration (n : ℕ) (ω : Fin n → ℝ) : WeakDual ℝ (Fin n → ℝ) :=
  StrongDual.toWeakDual
    ({ toFun := fun f => ∑ x : Fin n, ω x * f x
       map_add' := by intro f g; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
       map_smul' := by
         intro r f
         simp only [Pi.smul_apply, smul_eq_mul]
         calc
           (∑ x : Fin n, ω x * (r * f x)) = ∑ x : Fin n, r * (ω x * f x) := by
             apply Finset.sum_congr rfl; intro x hx; ring
           _ = r * ∑ x : Fin n, ω x * f x := by rw [Finset.mul_sum] }
      : (Fin n → ℝ) →L[ℝ] ℝ)
@[simp] theorem finiteFieldConfiguration_eval_single (n : ℕ) (ω : Fin n → ℝ) (x : Fin n) :
    finiteFieldConfiguration n ω (Pi.single x (1 : ℝ)) = ω x := by
  simp [finiteFieldConfiguration, StrongDual.toWeakDual_apply, Pi.single_apply,
    Finset.sum_ite_eq']
@[simp] theorem finiteSiteEmbedLift_configuration_eval
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (n : ℕ) (eval : Fin n → E →L[ℝ] ℝ) (ω : Fin n → ℝ) (f : E) :
    finiteSiteEmbedLift eval (finiteFieldConfiguration n ω) f = ∑ x : Fin n, ω x * eval x f := by
  rw [finiteSiteEmbedLift_eval]
  simp_rw [finiteFieldConfiguration_eval_single]
theorem finiteSiteEmbedLift_gaussian_second_moment
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (n : ℕ) (eval : Fin n → E →L[ℝ] ℝ) (f : E) :
    ∫ ω : Fin n → ℝ, (finiteSiteEmbedLift eval (finiteFieldConfiguration n ω) f) ^ 2
      ∂Pphi2Clean.LatticeGaussian.productGaussian n 1 = ∑ x : Fin n, (eval x f) ^ 2 := by
  rw [show (fun ω : Fin n → ℝ => (finiteSiteEmbedLift eval (finiteFieldConfiguration n ω) f) ^ 2) =
      (fun ω => (∑ x : Fin n, ω x * eval x f) ^ 2) by
        funext ω; rw [finiteSiteEmbedLift_configuration_eval]]
  rw [show (fun ω : Fin n → ℝ => (∑ x : Fin n, ω x * eval x f) ^ 2) =
      (fun ω => (∑ x : Fin n, eval x f * ω x) ^ 2) by
        funext ω; congr 1; apply Finset.sum_congr rfl; intro x hx; ring]
  simpa using (Pphi2Clean.LatticeGaussian.productGaussian_linear_second_moment_eq
    n 1 (fun x => eval x f))
end Pphi2Clean.Continuum
