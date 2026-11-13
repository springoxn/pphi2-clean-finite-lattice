import AImathPPhi2Clean.ArbitraryDimParameters
import AImathPPhi2Clean.RawAtomicGaussianArbitraryDim
import AImathPPhi2Clean.RawAtomicGaussianSiteIdentityArbitraryDim
import AImathPPhi2Clean.RawAtomicGaussianTargetTailArbitraryDim
import AImathPPhi2Clean.RawLiftDimensionArbitraryDim
import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section
namespace Pphi2Clean.ArbitraryDimGaussian
open Pphi2Clean.ArbitraryDim
variable [Parameters]
open Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice

def rawLiftSourceFielddimension {N : ℕ} [NeZero N] (ξ : FiniteConfig N) :
    Pphi2Clean.ArbitraryDimRawLift.Torus N → ℝ :=
  fun x => ξ (Pi.single (Fintype.equivFin (FinLatticeSites dimension N) x) (1 : ℝ))

theorem actualRawAtomicLift_eq_rawAtomicFourierLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hL : 0 < L) (ξ : FiniteConfig N) (k : Index) :
    actualRawAtomicLift N a L hL ξ k =
      Pphi2Clean.ArbitraryDimRawLift.rawAtomicFourierLift N a L
        (rawLiftSourceFielddimension ξ) k := by
  simpa [actualRawAtomicLift, rawFourierProbe, rawLiftSourceFielddimension,
    Pphi2Clean.ArbitraryDimRawLift.rawAtomicFourierLift,
    Pphi2Clean.ArbitraryDimRawLift.siteCoefficient,
    Pphi2Clean.ArbitraryDimRawLift.sitePhase,
    physicalRawLiftDim, rawProbeDim, rawAtomicLiftDim, rawSiteCoefficientDim,
    rawSitePhaseDim, rawFieldDim] using
      (physicalRawLiftDim_eq_site_sum dimension N a L hL ξ k)

theorem actualRawAtomicLift_target_weight_summable (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L)
    (ξ : FiniteConfig N) :
    Summable (fun k : Index => targetWeight k *
      ‖actualRawAtomicLift N a L hL ξ k‖ ^ 2) := by
  have hsource : Summable (fun k : Index =>
      Pphi2Clean.ArbitraryDimRawLift.energyWeight k *
        ‖Pphi2Clean.ArbitraryDimRawLift.rawAtomicFourierLift N a L
          (rawLiftSourceFielddimension ξ) k‖ ^ 2) := by
    have h := Pphi2Clean.ArbitraryDimRawLift.rawAtomicFourierLift_mem_energyCarrier
      N a L (le_of_lt ha) (rawLiftSourceFielddimension ξ)
    simpa [Pphi2Clean.ArbitraryDimRawLift.energyCarrier] using h
  have hratio (k : Index) : targetWeight k ≤
      Pphi2Clean.ArbitraryDimRawLift.energyWeight k := by
    have h := Pphi2Clean.ArbitraryDim.target_fourier_term_le_radius_factor k 0
      (by simpa using norm_nonneg k)
    simpa [targetWeight, Pphi2Clean.ArbitraryDimRawLift.energyWeight] using h
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
end Pphi2Clean.ArbitraryDimGaussian
