import AImathPPhi2Clean.PhysicalLatticeGaussianLaw
import AImathPPhi2Clean.LatticeGaussianContinuumConsumer
import AImathPPhi2Clean.RawLiftDimension122409
import AImathPPhi2Clean.RealFourierTestFunctions
import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section
namespace Pphi2Clean.Dim122409Gaussian
open Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice
abbrev ConfigDim (d N : ℕ) [NeZero N] := FiniteLatticeConfiguration (Fintype.card (FinLatticeSites d N))
def rawFieldDim {d N : ℕ} [NeZero N] (ξ : ConfigDim d N) : FinLatticeField d N :=
  fun x => ξ (Pi.single (Fintype.equivFin (FinLatticeSites d N) x) (1 : ℝ))
def rawProbeDim (d : ℕ) (L : ℝ) (hL : 0 < L) (k : Fin d → ℤ)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ)) : ℂ :=
  (ω (periodicCosineTest d L k hL) : ℂ) + (ω (periodicSineTest d L k hL) : ℂ) * Complex.I
def rawSitePhaseDim (d N : ℕ) [NeZero N] (a L : ℝ)
    (x : FinLatticeSites d N) (k : Fin d → ℤ) : ℝ :=
  (2 * Real.pi / L) * ∑ i, (k i : ℝ) * (a * ((x i).val : ℝ))
def rawSiteCoefficientDim (d N : ℕ) [NeZero N] (a L : ℝ)
    (x : FinLatticeSites d N) (k : Fin d → ℤ) : ℂ :=
  (a ^ d : ℂ) * Complex.exp ((rawSitePhaseDim d N a L x k : ℂ) * Complex.I)
def rawAtomicLiftDim (d N : ℕ) [NeZero N] (a L : ℝ)
    (field : FinLatticeField d N) (k : Fin d → ℤ) : ℂ :=
  ∑ x, (field x : ℂ) * rawSiteCoefficientDim d N a L x k
def physicalRawLiftDim (d N : ℕ) [NeZero N] (a L : ℝ) (hL : 0 < L)
    (ξ : ConfigDim d N) (k : Fin d → ℤ) : ℂ :=
  rawProbeDim d L hL k (latticeEmbedLift (physicalTestEval d N a) ξ)
theorem physicalRawLiftDim_eq_site_sum (d N : ℕ) [NeZero N]
    (a L : ℝ) (hL : 0 < L) (ξ : ConfigDim d N) (k : Fin d → ℤ) :
    physicalRawLiftDim d N a L hL ξ k = rawAtomicLiftDim d N a L (rawFieldDim ξ) k := by
  rw [physicalRawLiftDim]
  unfold rawProbeDim rawFieldDim rawAtomicLiftDim rawSiteCoefficientDim rawSitePhaseDim
  rw [latticeEmbedLift_eval, latticeEmbedLift_eval]
  simp [physicalTestEval, latticePhysicalPoint]
  let e := Fintype.equivFin (FinLatticeSites d N)
  let phase : FinLatticeSites d N → ℝ := fun x =>
    (2 * Real.pi / L) * ∑ i, (k i : ℝ) * (a * ((x i).val : ℝ))
  let cfun : FinLatticeSites d N → ℂ := fun x =>
    (ξ (Pi.single (e x) (1 : ℝ)) : ℂ) * ((a ^ d : ℂ) * Complex.cos (phase x))
  let sfun : FinLatticeSites d N → ℂ := fun x =>
    (ξ (Pi.single (e x) (1 : ℝ)) : ℂ) * ((a ^ d : ℂ) * Complex.sin (phase x))
  have hcos : (∑ j : Fin (Fintype.card (FinLatticeSites d N)), cfun (e.symm j)) = ∑ x, cfun x := by
    simpa [cfun, e] using (e.symm.sum_comp cfun)
  have hsin : (∑ j : Fin (Fintype.card (FinLatticeSites d N)), sfun (e.symm j)) = ∑ x, sfun x := by
    simpa [sfun, e] using (e.symm.sum_comp sfun)
  simp [cfun, phase, e] at hcos
  simp [sfun, phase, e] at hsin
  have hsum :
      (∑ x : FinLatticeSites d N, (cfun x + sfun x * Complex.I)) =
        ∑ x : FinLatticeSites d N,
          (ξ (Pi.single (e x) (1 : ℝ)) : ℂ) *
            ((a ^ d : ℂ) * Complex.exp ((phase x : ℂ) * Complex.I)) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [cfun, sfun, phase, Complex.exp_mul_I]
    ring
  calc
    _ = (∑ x, cfun x) + (∑ x, sfun x) * Complex.I := by rw [hcos, hsin]; simp [cfun, sfun, phase, e]
    _ = ∑ x, (cfun x + sfun x * Complex.I) := by simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    _ = _ := by simpa [cfun, sfun, phase, e] using hsum
#print axioms physicalRawLiftDim_eq_site_sum
end Pphi2Clean.Dim122409Gaussian
