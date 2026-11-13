import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

noncomputable section
open scoped ComplexConjugate InnerProductSpace lp
namespace Pphi2Clean.Continuum

abbrev MassiveEnergy (ι : Type*) := lp (fun _ : ι => ℂ) 2

/-- A bounded coefficient multiplier, constructed without a Green series. -/
def energyMultiplier {ι : Type*} (a : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k, ‖a k‖ ≤ C) : MassiveEnergy ι →L[ℂ] MassiveEnergy ι :=
  lp.mapCLM 2 (fun k => a k • (ContinuousLinearMap.id ℂ ℂ)) hC
    (fun k => by rw [norm_smul, ContinuousLinearMap.norm_id]; simpa using ha k)

@[simp] theorem energyMultiplier_apply {ι : Type*} (a : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k, ‖a k‖ ≤ C) (h : MassiveEnergy ι) (k : ι) :
    energyMultiplier a C hC ha h k = a k * h k := rfl

/-- The energy-to-physical coefficient embedding has strictly positive real
weights. This abstract representation permits arbitrary massive dispersions. -/
structure MassiveEnergyEmbedding (ι : Type*) where
  weight : ι → ℝ
  weight_pos : ∀ k, 0 < weight k
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  weight_le : ∀ k, weight k ≤ bound

namespace MassiveEnergyEmbedding
variable {ι : Type*} (A : MassiveEnergyEmbedding ι)

def inclusion : MassiveEnergy ι →L[ℂ] MassiveEnergy ι :=
  energyMultiplier (fun k => (A.weight k : ℂ)) A.bound A.bound_nonneg
    (fun k => by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (A.weight_pos k)]
      using A.weight_le k)

@[simp] theorem inclusion_apply (h : MassiveEnergy ι) (k : ι) :
    A.inclusion h k = (A.weight k : ℂ) * h k := rfl

theorem inclusion_injective : Function.Injective A.inclusion := by
  intro h v heq
  apply lp.ext
  funext k
  have hk := congrArg (fun x : MassiveEnergy ι => x k) heq
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (A.weight_pos k).ne') hk

/-- Riesz solution in energy coordinates. The adjoint construction is independent
of any pre-existing Fourier Green pairing or infinite series. -/
def solve (g : MassiveEnergy ι) : MassiveEnergy ι := A.inclusion.adjoint g

theorem solve_weak (g v : MassiveEnergy ι) :
    ⟪A.solve g, v⟫_ℂ = ⟪g, A.inclusion v⟫_ℂ :=
  A.inclusion.adjoint_inner_left v g

theorem weak_unique (g h : MassiveEnergy ι)
    (hh : ∀ v, ⟪h, v⟫_ℂ = ⟪g, A.inclusion v⟫_ℂ) : h = A.solve g := by
  apply ext_inner_right ℂ
  intro v
  exact (hh v).trans (A.solve_weak g v).symm

theorem existsUnique_weak (g : MassiveEnergy ι) :
    ∃! h : MassiveEnergy ι, ∀ v, ⟪h, v⟫_ℂ = ⟪g, A.inclusion v⟫_ℂ :=
  ⟨A.solve g, A.solve_weak g, fun h hh => A.weak_unique g h hh⟩

theorem solve_apply (g : MassiveEnergy ι) (k : ι) :
    A.solve g k = (A.weight k : ℂ) * g k := by
  classical
  have hs : A.inclusion (lp.single 2 k (1 : ℂ)) =
      lp.single 2 k (A.weight k : ℂ) := by
    apply lp.ext
    funext j
    by_cases hj : j = k
    · subst j; simp
    · simp [lp.single_apply, hj, Ne.symm hj]
  have h := A.inclusion.adjoint_inner_right (lp.single 2 k (1 : ℂ)) g
  rw [hs, lp.inner_single_left, lp.inner_single_left] at h
  change A.solve g k * star (1 : ℂ) = g k * star (A.weight k : ℂ) at h
  simpa only [map_one, mul_one, one_mul, Complex.star_def, Complex.conj_ofReal, mul_comm] using h

end MassiveEnergyEmbedding
/-- Finite-support energy vectors converge in the energy norm. -/
theorem finiteSupport_tendsto {ι : Type*} [DecidableEq ι] (h : MassiveEnergy ι) :
    Filter.Tendsto (fun s : Finset ι => ∑ k ∈ s, lp.single 2 k (h k))
      Filter.atTop (nhds h) :=
  lp.hasSum_single (by norm_num) h

/-- Massive coefficient model with physical weight lambda^(-1/2). -/
def massiveEmbedding {ι : Type*} (mass : ℝ) (hmass : 0 < mass)
    (lam : ι → ℝ) (hlam : ∀ k, mass ^ 2 ≤ lam k) : MassiveEnergyEmbedding ι where
  weight k := (Real.sqrt (lam k))⁻¹
  weight_pos k := inv_pos.mpr (Real.sqrt_pos.mpr ((sq_pos_of_pos hmass).trans_le (hlam k)))
  bound := mass⁻¹
  bound_nonneg := (inv_pos.mpr hmass).le
  weight_le k := by
    apply (inv_le_inv₀ (Real.sqrt_pos.mpr ((sq_pos_of_pos hmass).trans_le (hlam k))) hmass).mpr
    exact (Real.le_sqrt hmass.le (le_trans (sq_nonneg mass) (hlam k))).mpr (hlam k)

end Pphi2Clean.Continuum
