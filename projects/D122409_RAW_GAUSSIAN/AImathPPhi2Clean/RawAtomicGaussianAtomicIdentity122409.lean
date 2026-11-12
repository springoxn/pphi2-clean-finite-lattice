import AImathPPhi2Clean.RawAtomicGaussian122409
import AImathPPhi2Clean.RawAtomicGaussianSiteIdentity122409
import AImathPPhi2Clean.RawAtomicGaussianTargetTail122409
import AImathPPhi2Clean.RawLiftDimension122409
import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section
namespace Pphi2Clean.Dim122409Gaussian
open Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice

def rawLiftSourceField122409 {N : ℕ} [NeZero N] (ξ : FiniteConfig N) :
    Pphi2Clean.Dim122409RawLift.Torus N → ℝ :=
  fun x => ξ (Pi.single (Fintype.equivFin (FinLatticeSites 122409 N) x) (1 : ℝ))

theorem actualRawAtomicLift_eq_rawAtomicFourierLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hL : 0 < L) (ξ : FiniteConfig N) (k : Index) :
    actualRawAtomicLift N a L hL ξ k =
      Pphi2Clean.Dim122409RawLift.rawAtomicFourierLift N a L
        (rawLiftSourceField122409 ξ) k := by
  simpa [actualRawAtomicLift, rawFourierProbe, rawLiftSourceField122409,
    Pphi2Clean.Dim122409RawLift.rawAtomicFourierLift,
    Pphi2Clean.Dim122409RawLift.siteCoefficient,
    Pphi2Clean.Dim122409RawLift.sitePhase,
    physicalRawLiftDim, rawProbeDim, rawAtomicLiftDim, rawSiteCoefficientDim,
    rawSitePhaseDim, rawFieldDim] using
      (physicalRawLiftDim_eq_site_sum 122409 N a L hL ξ k)

theorem actualRawAtomicLift_target_weight_summable (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L)
    (ξ : FiniteConfig N) :
    Summable (fun k : Index => targetWeight k *
      ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2) := by
  have hsource : Summable (fun k : Index =>
      Pphi2Clean.Dim122409RawLift.energyWeight k *
        ‖Pphi2Clean.Dim122409RawLift.rawAtomicFourierLift N a L
          (rawLiftSourceField122409 ξ) k‖ ^ 2) := by
    have h := Pphi2Clean.Dim122409RawLift.rawAtomicFourierLift_mem_energyCarrier
      N a L (le_of_lt ha) (rawLiftSourceField122409 ξ)
    simpa [Pphi2Clean.Dim122409RawLift.energyCarrier] using h
  have hratio (k : Index) : targetWeight k ≤
      Pphi2Clean.Dim122409RawLift.energyWeight k := by
    have h := Pphi2Clean.DimensionFreeProbe.target_fourier_term_le_radius_factor k 0
      (by simpa using norm_nonneg k)
    simpa [targetWeight, Pphi2Clean.Dim122409RawLift.energyWeight] using h
  apply hsource.of_nonneg_of_le
  · intro k
    exact mul_nonneg (by
      unfold targetWeight
      have hb : 0 ≤ 1 + ‖k‖ := by linarith [norm_nonneg k]
      exact Real.rpow_nonneg hb _) (sq_nonneg _)
  · intro k
    rw [actualRawAtomicLift_eq_rawAtomicFourierLift N a L hL ξ k]
    exact mul_le_mul_of_nonneg_right (hratio k) (sq_nonneg _)

#print axioms actualRawAtomicLift_eq_rawAtomicFourierLift
#print axioms actualRawAtomicLift_target_weight_summable
end Pphi2Clean.Dim122409Gaussian
