import AImathPPhi2Clean.PeriodicMassiveWeakSolver
import Mathlib.Analysis.Fourier.AddCircleMulti

noncomputable section
open scoped InnerProductSpace
namespace Pphi2Clean.Continuum

/-! Transport of the independently constructed energy Riesz solver to a Hilbert
space with a specified orthonormal basis. No Green-series definition is used.
The periodic specialization uses the complete multivariate torus Fourier basis. -/

namespace MassiveEnergyEmbedding
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] (A : MassiveEnergyEmbedding ι) (b : HilbertBasis ι ℂ E)

/-- The physical Hilbert-space value of an energy vector. -/
def lift (h : MassiveEnergy ι) : E := b.repr.symm (A.inclusion h)

/-- The bounded map from completed energy coordinates to physical L2. -/
def liftCLM : MassiveEnergy ι →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp A.inclusion

@[simp] theorem liftCLM_apply (h : MassiveEnergy ι) : A.liftCLM b h = A.lift b h := rfl

/-- The weak solution represented in energy coordinates. -/
def solveIn (g : E) : MassiveEnergy ι := A.solve (b.repr g)

/-- The physical weak resolvent, obtained from the energy Riesz solution. -/
def resolventIn (g : E) : E := A.lift b (A.solveIn b g)

/-- The same resolvent as a bounded linear operator. -/
def resolventInCLM : E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.inclusion.comp
      (A.inclusion.adjoint.comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] theorem resolventInCLM_apply (g : E) :
    A.resolventInCLM b g = A.resolventIn b g := rfl

@[simp] theorem repr_lift (h : MassiveEnergy ι) :
    b.repr (A.lift b h) = A.inclusion h := b.repr.apply_symm_apply _

theorem lift_injective : Function.Injective (A.lift b) := by
  intro h v heq
  apply A.inclusion_injective
  simpa only [repr_lift] using congrArg b.repr heq

/-- The weak equation tests every energy vector, not only individual modes. -/
theorem solveIn_weak (g : E) (v : MassiveEnergy ι) :
    ⟪A.solveIn b g, v⟫_ℂ = ⟪g, A.lift b v⟫_ℂ := by
  rw [← b.repr.inner_map_map g (A.lift b v), repr_lift]
  exact A.solve_weak (b.repr g) v

theorem solveIn_unique (g : E) (h : MassiveEnergy ι)
    (hh : ∀ v, ⟪h, v⟫_ℂ = ⟪g, A.lift b v⟫_ℂ) : h = A.solveIn b g := by
  apply ext_inner_right ℂ
  intro v
  exact (hh v).trans (A.solveIn_weak b g v).symm

theorem existsUnique_weak_in (g : E) :
    ∃! h : MassiveEnergy ι, ∀ v, ⟪h, v⟫_ℂ = ⟪g, A.lift b v⟫_ℂ :=
  ⟨A.solveIn b g, A.solveIn_weak b g, fun h hh => A.solveIn_unique b g h hh⟩

/-- A physical weak solution has an energy representative and satisfies the
weak equation against the entire energy space. -/
def IsWeakValue (g u : E) : Prop :=
  ∃ h : MassiveEnergy ι, A.lift b h = u ∧
    ∀ v, ⟪h, v⟫_ℂ = ⟪g, A.lift b v⟫_ℂ

theorem existsUnique_weak_value (g : E) :
    ∃! u : E, A.IsWeakValue b g u := by
  refine ⟨A.resolventIn b g, ⟨A.solveIn b g, rfl, A.solveIn_weak b g⟩, ?_⟩
  rintro u ⟨h, hu, hh⟩
  rw [A.solveIn_unique b g h hh] at hu
  exact hu.symm

@[simp] theorem repr_resolventIn_apply (g : E) (k : ι) :
    b.repr (A.resolventIn b g) k = (A.weight k : ℂ) ^ 2 * b.repr g k := by
  simp only [resolventIn, repr_lift, inclusion_apply, solveIn, solve_apply]
  ring

/-- The spectral formula is derived from the weak solver through Parseval. -/
theorem inner_resolventIn (f g : E) :
    ⟪f, A.resolventIn b g⟫_ℂ =
      ∑' k, star (b.repr f k) * ((A.weight k : ℂ) ^ 2 * b.repr g k) := by
  rw [← b.repr.inner_map_map f (A.resolventIn b g), lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [repr_resolventIn_apply]
  simp only [RCLike.inner_apply, Complex.star_def]
  ring

/-- A finite energy coordinate is an actual finite basis mode in physical L2. -/
theorem lift_single [DecidableEq ι] (k : ι) (a : ℂ) :
    A.lift b (lp.single 2 k a) = ((A.weight k : ℂ) * a) • b k := by
  apply b.repr.injective
  rw [repr_lift, map_smul, b.repr_self]
  apply lp.ext
  funext j
  by_cases hj : j = k
  · subst j
    simp
  · simp [inclusion_apply, lp.single_apply, hj, Ne.symm hj]

/-- The actual finite-mode approximants converge to the completed energy value. -/
theorem hasSum_lift_single [DecidableEq ι] (h : MassiveEnergy ι) :
    HasSum (fun k => ((A.weight k : ℂ) * h k) • b k) (A.lift b h) := by
  have hs := (A.liftCLM b).hasSum (lp.hasSum_single (by norm_num) h)
  simpa only [liftCLM_apply, lift_single] using hs

end MassiveEnergyEmbedding

/-- Periodic L2 with probability Haar measure. Physical volume pairings carry
an additional factor L^d. -/
abbrev PeriodicL2 (d : ℕ) :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.Measure.pi
    (fun _ : Fin d => (AddCircle.haarAddCircle : MeasureTheory.Measure UnitAddCircle)))

/-- The complete multidimensional Fourier basis on the actual periodic L2
space, including dimension zero. -/
def periodicFourierHilbertBasis (d : ℕ) :
    HilbertBasis (Fin d → ℤ) ℂ (PeriodicL2 d) := by
  letI : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  exact UnitAddTorus.mFourierBasis

end Pphi2Clean.Continuum
