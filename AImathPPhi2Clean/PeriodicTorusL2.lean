import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Algebra.Module.PointwisePi
import Mathlib.Algebra.Order.Field.Pointwise

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory Set
open scoped Pointwise

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Measurable unit-cell representative, with no continuous descent requirement. -/
def physicalTorusRepresentative (d : ℕ) (x : UnitAddTorus (Fin d)) : Fin d → ℝ :=
  (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => 0) x).val

theorem measurable_physicalTorusRepresentative (d : ℕ) :
    Measurable (physicalTorusRepresentative d) :=
  measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => 0)).measurable

/-- Physical test evaluated at its measurable representative. -/
def physicalTorusTest (d : ℕ) (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (x : UnitAddTorus (Fin d)) : ℂ :=
  f (L • physicalTorusRepresentative d x)

theorem measurable_physicalTorusTest (d : ℕ) (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Measurable (physicalTorusTest d L f) := by
  exact Complex.continuous_ofReal.measurable.comp
    (f.continuous.measurable.comp ((measurable_physicalTorusRepresentative d).const_smul L))

theorem physicalTorusTest_memLp (d : ℕ) (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    MemLp (physicalTorusTest d L f) 2 (volume : Measure (UnitAddTorus (Fin d))) := by
  apply MemLp.of_bound (measurable_physicalTorusTest d L f).aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [physicalTorusTest, Complex.norm_real] using f.norm_coe_le_norm (L • physicalTorusRepresentative d x))

/-- L2 realization of a physical-volume test on the probability-normalized torus. -/
def physicalTorusTestL2 (d : ℕ) (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))) :=
  (physicalTorusTest_memLp d L f).toLp (physicalTorusTest d L f)

theorem coeFn_physicalTorusTestL2 (d : ℕ) (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    physicalTorusTestL2 d L f =ᵐ[volume] physicalTorusTest d L f :=
  (physicalTorusTest_memLp d L f).coeFn_toLp

theorem physicalTorusTestL2_repr_eq_mFourierCoeff (d : ℕ) (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierBasis.repr (physicalTorusTestL2 d L f) k =
      UnitAddTorus.mFourierCoeff (physicalTorusTest d L f) k := by
  rw [UnitAddTorus.mFourierBasis_repr]
  apply integral_congr_ae
  filter_upwards [coeFn_physicalTorusTestL2 d L f] with x hx
  rw [hx]

/-- On the chosen half-open cell the representative returns the original point. -/
theorem physicalTorusRepresentative_coe (d : ℕ) (x : Fin d → ℝ)
    (hx : ∀ i, x i ∈ Ioc (0 : ℝ) 1) :
    physicalTorusRepresentative d (fun i => (x i : UnitAddCircle)) = x := by
  let y : {x : Fin d → ℝ // ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)} := ⟨x, by simpa using hx⟩
  have h := (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => 0)).apply_symm_apply y
  exact congrArg Subtype.val h

/-- Continuous physical phases agree with Mathlib's torus monomials. -/
theorem torusFourierPhase_smul_eq_mFourier (d : ℕ) (L : ℝ) (hL : L ≠ 0)
    (k : Fin d → ℤ) (x : Fin d → ℝ) :
    torusFourierPhase d L k (L • x) =
      UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply, div_one]
  rw [← Complex.exp_sum]
  unfold torusFourierPhase
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [show (L : ℂ) ≠ 0 by exact_mod_cast hL]
  <;> ring

/-- The coefficient of the L2 representative is the unit-cell physical integral. -/
theorem physicalTorusTestL2_repr_unit_integral (d : ℕ) (L : ℝ) (hL : L ≠ 0)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierBasis.repr (physicalTorusTestL2 d L f) k =
      ∫ x in Set.pi Set.univ (fun _ : Fin d => Ioc (0 : ℝ) 1),
        (f (L • x) : ℂ) * torusFourierPhase d L (-k) (L • x) := by
  rw [physicalTorusTestL2_repr_eq_mFourierCoeff, UnitAddTorus.mFourierCoeff_eq_integral _ k 0]
  simp only [Pi.zero_apply, zero_add]
  rw [show {x : Fin d → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} =
    Set.pi Set.univ (fun _ : Fin d => Ioc (0 : ℝ) 1) by ext x; simp]
  apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
  intro x hx
  have hx' : ∀ i, x i ∈ Ioc (0 : ℝ) 1 := by simpa using hx
  dsimp only
  rw [smul_eq_mul, physicalTorusTest, physicalTorusRepresentative_coe d x hx',
    torusFourierPhase_smul_eq_mFourier d L hL]
  exact mul_comm _ _

/-- Exact probability/physical-volume normalization of Fourier coordinates. -/
theorem physicalTorusTestL2_repr (d : ℕ) (L : ℝ) (hL : 0 < L)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierBasis.repr (physicalTorusTestL2 d L f) k =
      (L : ℂ)⁻¹ ^ d * torusFourierCoefficient d L f k := by
  rw [physicalTorusTestL2_repr_unit_integral d L hL.ne']
  have hae : (Set.pi Set.univ (fun _ : Fin d => Ioc (0 : ℝ) 1)) =ᵐ[volume]
      Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) 1) := by
    rw [volume_pi]
    exact Measure.pi_Ioc_ae_eq_pi_Icc
  rw [setIntegral_congr_set hae]
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (Fin d → ℝ))
    (fun x : Fin d → ℝ => (f x : ℂ) * torusFourierPhase d L (-k) x)
    (Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) 1)) hL
  have hset : L • (Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) 1)) =
      Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) L) := by
    rw [smul_univ_pi]
    change Set.pi Set.univ (fun _ : Fin d => L • Icc (0 : ℝ) 1) = _
    simp [LinearOrderedField.smul_Icc hL]
  rw [hset] at hscale
  simpa [torusFourierCoefficient, Module.finrank_pi, smul_eq_mul, Complex.ofReal_inv,
    Complex.ofReal_pow, inv_pow] using hscale

end Pphi2Clean.Continuum
