import AImathPPhi2Clean.ConcreteLatticeCovariance
import AImathPPhi2Clean.PeriodicFourierLaplacian
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
namespace Pphi2Clean.Continuum
open Pphi2Clean.UpstreamLattice

/-- Complexification of the actual real mass matrix. -/
def complexLatticeMassOperator (d N : ℕ) [NeZero N] (a mass : ℝ) :
    (FinLatticeSites d N → ℂ) →ₗ[ℂ] (FinLatticeSites d N → ℂ) :=
  Matrix.mulVecLin (fun x y => (massOperatorMatrix d N a mass x y : ℂ))

@[simp] theorem complexLatticeMassOperator_re
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (f : FinLatticeSites d N → ℂ) (x : FinLatticeSites d N) :
    (complexLatticeMassOperator d N a mass f x).re =
      massOperator d N a mass (fun y => (f y).re) x := by
  change (∑ y : FinLatticeSites d N,
    (massOperatorMatrix d N a mass x y : ℂ) * f y).re = _
  rw [massOperator_eq_matrix_mulVec]
  simp [Matrix.mulVec, dotProduct]

@[simp] theorem complexLatticeMassOperator_im
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (f : FinLatticeSites d N → ℂ) (x : FinLatticeSites d N) :
    (complexLatticeMassOperator d N a mass f x).im =
      massOperator d N a mass (fun y => (f y).im) x := by
  change (∑ y : FinLatticeSites d N,
    (massOperatorMatrix d N a mass x y : ℂ) * f y).im = _
  rw [massOperator_eq_matrix_mulVec]
  simp [Matrix.mulVec, dotProduct]

/-- The matrix complexification agrees with the periodic finite differences. -/
theorem complexLatticeMassOperator_apply
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (f : FinLatticeSites d N → ℂ) (x : FinLatticeSites d N) :
    complexLatticeMassOperator d N a mass f x =
      -(a : ℂ)⁻¹ ^ 2 * ∑ i : Fin d,
        (f (fun j => if j = i then x j + 1 else x j) +
         f (fun j => if j = i then x j - 1 else x j) - 2 * f x) +
      (mass : ℂ) ^ 2 * f x := by
  apply Complex.ext <;>
    simp [complexLatticeMassOperator_re, complexLatticeMassOperator_im,
      massOperator, finiteLaplacian, finiteLaplacianLM, finiteLaplacianFun,
      ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]

theorem complexLatticeMassOperator_injective
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Function.Injective (complexLatticeMassOperator d N a mass) := by
  intro f g h
  have hr : (fun x => (f x).re) = (fun x => (g x).re) := by
    apply latticeMassOperator_injective d N a mass ha hmass
    funext x
    simpa only [complexLatticeMassOperator_re] using
      congrArg Complex.re (congrFun h x)
  have hi : (fun x => (f x).im) = (fun x => (g x).im) := by
    apply latticeMassOperator_injective d N a mass ha hmass
    funext x
    simpa only [complexLatticeMassOperator_im] using
      congrArg Complex.im (congrFun h x)
  funext x
  exact Complex.ext (congrFun hr x) (congrFun hi x)

/-- Character form of the mass symbol, with no trigonometric assumptions. -/
def latticeFourierMassSymbol (d N : ℕ) [NeZero N]
    (a mass : ℝ) (p : FinLatticeSites d N) : ℂ :=
  (mass : ℂ) ^ 2 - ∑ i : Fin d, periodicFourierEigenvalue d N a p i

theorem complexLatticeMassOperator_character
    (d N : ℕ) [NeZero N] (a mass : ℝ) (p : FinLatticeSites d N) :
    complexLatticeMassOperator d N a mass (periodicFourierCharacter d N p) =
      latticeFourierMassSymbol d N a mass p • periodicFourierCharacter d N p := by
  funext x
  rw [complexLatticeMassOperator_apply]
  exact complexFiniteMassOperator_character d N a mass p x

/-- Nonvanishing follows from positivity of the actual real operator, not
from an assumed Fourier dispersion formula. -/
theorem latticeFourierMassSymbol_ne_zero
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (p : FinLatticeSites d N) :
    latticeFourierMassSymbol d N a mass p ≠ 0 := by
  intro hz
  have hk : complexLatticeMassOperator d N a mass
      (periodicFourierCharacter d N p) =
      complexLatticeMassOperator d N a mass 0 := by
    rw [complexLatticeMassOperator_character, hz, zero_smul, map_zero]
  have hc := complexLatticeMassOperator_injective d N a mass ha hmass hk
  have h0 := congrFun hc 0
  simpa using h0

/-- Explicit Fourier inverse of the finite mass operator. -/
def fourierLatticeMassResolvent (d N : ℕ) [NeZero N] (a mass : ℝ)
    (f : FinLatticeSites d N → ℂ) : FinLatticeSites d N → ℂ :=
  (N : ℂ)⁻¹ ^ d • ∑ p : FinLatticeSites d N,
    (finiteFourierCoefficient d N f p / latticeFourierMassSymbol d N a mass p) •
      periodicFourierCharacter d N p

theorem complexLatticeMassOperator_fourierResolvent
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f : FinLatticeSites d N → ℂ) :
    complexLatticeMassOperator d N a mass
      (fourierLatticeMassResolvent d N a mass f) = f := by
  unfold fourierLatticeMassResolvent
  simp only [map_smul, map_sum, complexLatticeMassOperator_character, smul_smul]
  have hc (p : FinLatticeSites d N) :
      finiteFourierCoefficient d N f p / latticeFourierMassSymbol d N a mass p *
        latticeFourierMassSymbol d N a mass p = finiteFourierCoefficient d N f p :=
    div_mul_cancel₀ _ (latticeFourierMassSymbol_ne_zero d N a mass ha hmass p)
  simp_rw [hc]
  funext x
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using
    finiteFourier_inversion d N f x

/-- On real input, the real part of the Fourier inverse equals the inverse
of the original real mass operator. -/
theorem fourierResolvent_re_eq_latticeMassResolvent
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (g : FinLatticeField d N) :
    (fun x => (fourierLatticeMassResolvent d N a mass (fun y => (g y : ℂ)) x).re) =
      latticeMassResolvent d N a mass ha hmass g := by
  apply eq_latticeMassResolvent_of_massOperator_eq d N a mass ha hmass
  funext x
  have h := congrArg (fun u : FinLatticeSites d N → ℂ => (u x).re)
    (complexLatticeMassOperator_fourierResolvent d N a mass ha hmass
      (fun y => (g y : ℂ)))
  simpa only [complexLatticeMassOperator_re, Complex.ofReal_re] using h

/-- The Fourier solution of a real mass equation has zero imaginary part. -/
theorem fourierResolvent_im_eq_zero
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (g : FinLatticeField d N) :
    (fun x => (fourierLatticeMassResolvent d N a mass (fun y => (g y : ℂ)) x).im) = 0 := by
  apply latticeMassOperator_injective d N a mass ha hmass
  funext x
  have h := congrArg (fun u : FinLatticeSites d N → ℂ => (u x).im)
    (complexLatticeMassOperator_fourierResolvent d N a mass ha hmass
      (fun y => (g y : ℂ)))
  simpa only [complexLatticeMassOperator_im, Complex.ofReal_im, map_zero,
    Pi.zero_apply] using h

/-- Identification of the whole complex Fourier inverse on real input. -/
theorem fourierResolvent_eq_real_massResolvent
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (g : FinLatticeField d N) :
    fourierLatticeMassResolvent d N a mass (fun y => (g y : ℂ)) =
      fun x => (latticeMassResolvent d N a mass ha hmass g x : ℂ) := by
  funext x
  apply Complex.ext
  · exact congrFun (fourierResolvent_re_eq_latticeMassResolvent d N a mass ha hmass g) x
  · exact congrFun (fourierResolvent_im_eq_zero d N a mass ha hmass g) x

/-- Pairing a site field with the explicit inverse gives opposite-frequency
Fourier coefficients with the exact counting normalization. -/
theorem site_pair_fourierMassResolvent
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (f g : FinLatticeSites d N → ℂ) :
    (∑ x : FinLatticeSites d N, f x * fourierLatticeMassResolvent d N a mass g x) =
      (N : ℂ)⁻¹ ^ d * ∑ p : FinLatticeSites d N,
        finiteFourierCoefficient d N f (-p) *
          (finiteFourierCoefficient d N g p / latticeFourierMassSymbol d N a mass p) := by
  unfold fourierLatticeMassResolvent
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  calc
    (∑ x : FinLatticeSites d N, f x * ((N : ℂ)⁻¹ ^ d *
      ∑ p : FinLatticeSites d N,
        (finiteFourierCoefficient d N g p / latticeFourierMassSymbol d N a mass p) *
          periodicFourierCharacter d N p x)) =
        (N : ℂ)⁻¹ ^ d * ∑ x : FinLatticeSites d N, ∑ p : FinLatticeSites d N,
          f x * (finiteFourierCoefficient d N g p / latticeFourierMassSymbol d N a mass p) *
            periodicFourierCharacter d N p x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (N : ℂ)⁻¹ ^ d * ∑ p : FinLatticeSites d N, ∑ x : FinLatticeSites d N,
          f x * (finiteFourierCoefficient d N g p / latticeFourierMassSymbol d N a mass p) *
            periodicFourierCharacter d N p x := by rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      simp only [finiteFourierCoefficient, neg_neg, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- Existing GJ covariance as an explicit Fourier sum, before physical test
sampling. No spectral identification hypotheses are supplied by the caller. -/
theorem latticeCovarianceGJ_inner_eq_fourier
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f g : FinLatticeField d N) :
    @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
      (latticeCovarianceGJ d N a mass ha hmass f)
      (latticeCovarianceGJ d N a mass ha hmass g) =
      (a ^ d : ℝ)⁻¹ * ((N : ℂ)⁻¹ ^ d * ∑ p : FinLatticeSites d N,
        star (finiteFourierCoefficient d N (fun x => (f x : ℂ)) p) *
          (finiteFourierCoefficient d N (fun x => (g x : ℂ)) p /
            latticeFourierMassSymbol d N a mass p)).re := by
  rw [latticeCovarianceGJ_inner_eq_massResolvent]
  congr 1
  have h := site_pair_fourierMassResolvent d N a mass
    (fun x => (f x : ℂ)) (fun x => (g x : ℂ))
  have hc (p : FinLatticeSites d N) :
      finiteFourierCoefficient d N (fun x => (f x : ℂ)) (-p) =
        star (finiteFourierCoefficient d N (fun x => (f x : ℂ)) p) := by
    simpa only [Complex.star_def, Complex.conj_ofReal] using
      finiteFourierCoefficient_star_neg d N (fun x => (f x : ℂ)) p
  simp_rw [hc] at h
  rw [← h, fourierResolvent_eq_real_massResolvent d N a mass ha hmass]
  simp

end Pphi2Clean.Continuum
