import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open scoped BigOperators
open Complex
namespace Pphi2Clean.Continuum

/-- The physical-coordinate derivative of an actual torus Fourier monomial. -/
theorem hasDerivAt_mFourier_physicalCoordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℝ) (k : ι → ℤ) (z : UnitAddTorus ι) (i : ι) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => UnitAddTorus.mFourier k (Function.update z i ((s / L : ℝ) : UnitAddCircle)))
      (((2 * Real.pi / L) * (k i : ℝ) : ℝ) * Complex.I *
        UnitAddTorus.mFourier k (Function.update z i ((t / L : ℝ) : UnitAddCircle))) t := by
  classical
  have hmode := (hasDerivAt_fourier (1 : ℝ) (k i) (t / L)).scomp t
    ((hasDerivAt_id t).div_const L)
  let c : ℂ := ∏ j ∈ Finset.univ.erase i, fourier (k j) (z j)
  have heq (s : ℝ) :
      UnitAddTorus.mFourier k (Function.update z i ((s / L : ℝ) : UnitAddCircle)) =
        fourier (k i) ((s / L : ℝ) : UnitAddCircle) * c := by
    change (∏ j : ι, fourier (k j) (Function.update z i _ j)) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  simp_rw [heq]
  simp only [Function.comp_def, id_eq, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one] at hmode
  convert hmode.mul_const c using 1 <;> first | rfl | (push_cast; ring)

/-- Finite trigonometric polynomials have their classical coordinate gradient
obtained by multiplying each mode by 2 pi i k_i / L. -/
theorem hasDerivAt_trigPolynomial_physicalCoordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℝ) (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ)
    (z : UnitAddTorus ι) (i : ι) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∑ k ∈ S, a k * UnitAddTorus.mFourier k
        (Function.update z i ((s / L : ℝ) : UnitAddCircle)))
      (∑ k ∈ S, a k * (((2 * Real.pi / L) * (k i : ℝ) : ℝ) * Complex.I *
        UnitAddTorus.mFourier k (Function.update z i ((t / L : ℝ) : UnitAddCircle)))) t := by
  apply HasDerivAt.fun_sum
  intro k hk
  exact (hasDerivAt_mFourier_physicalCoordinate L k z i t).const_mul (a k)

end Pphi2Clean.Continuum
