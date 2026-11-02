import AImathPPhi2Clean.RealLatticeSpectralCovariance
import AImathPPhi2Clean.ConcreteLatticeOperator

noncomputable section
namespace Pphi2Clean.Continuum
open Pphi2Clean.UpstreamLattice

/-- Clean migration of the upstream finite-lattice covariance. -/
noncomputable def latticeCovariance
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    (FinLatticeSites d N → ℝ) →L[ℝ]
      EuclideanSpace ℝ (FinLatticeSites d N) :=
  spectralCovariance (spectralData d N a mass ha hmass)

/-- GJ-normalized clean migration of the upstream finite-lattice covariance. -/
noncomputable def latticeCovarianceGJ
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    (FinLatticeSites d N → ℝ) →L[ℝ]
      EuclideanSpace ℝ (FinLatticeSites d N) :=
  spectralCovarianceGJ a d ha (spectralData d N a mass ha hmass)

theorem latticeCovariance_inner
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeSites d N → ℝ) :
    @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
      (latticeCovariance d N a mass ha hmass f)
      (latticeCovariance d N a mass ha hmass g) =
      ∑ k : FinLatticeSites d N,
        (massEigenvalues d N a mass k)⁻¹ *
          (∑ x, (massEigenvectorBasis d N a mass k :
            EuclideanSpace ℝ (FinLatticeSites d N)) x * f x) *
          (∑ x, (massEigenvectorBasis d N a mass k :
            EuclideanSpace ℝ (FinLatticeSites d N)) x * g x) := by
  exact spectralCovariance_inner (spectralData d N a mass ha hmass) f g

theorem latticeCovarianceGJ_inner
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeSites d N → ℝ) :
    @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
      (latticeCovarianceGJ d N a mass ha hmass f)
      (latticeCovarianceGJ d N a mass ha hmass g) =
      (a ^ d : ℝ)⁻¹ *
        @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
          (latticeCovariance d N a mass ha hmass f)
          (latticeCovariance d N a mass ha hmass g) := by
  exact spectralCovarianceGJ_inner a d ha
    (spectralData d N a mass ha hmass) f g

/-- Positivity makes the actual finite-difference mass operator injective. -/
theorem latticeMassOperator_injective
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Function.Injective (massOperator d N a mass) := by
  intro f g h
  have hz : massOperator d N a mass (f - g) = 0 := by
    rw [map_sub, h, sub_self]
  have he : f - g = 0 := by
    by_contra hn
    have hp := massOperator_pos_def d N a mass ha hmass (f - g) hn
    rw [hz] at hp
    simpa using hp
  exact sub_eq_zero.mp he

/-- The inverse of the actual finite mass operator, obtained from positivity
and finite dimensionality; no choice of Fourier basis enters this definition. -/
def latticeMassResolvent (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    FinLatticeField d N →ₗ[ℝ] FinLatticeField d N :=
  (LinearEquiv.ofInjectiveEndo (massOperator d N a mass).toLinearMap
    (latticeMassOperator_injective d N a mass ha hmass)).symm.toLinearMap

@[simp] theorem massOperator_latticeMassResolvent
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (g : FinLatticeField d N) :
    massOperator d N a mass (latticeMassResolvent d N a mass ha hmass g) = g := by
  exact (LinearEquiv.ofInjectiveEndo (massOperator d N a mass).toLinearMap
    (latticeMassOperator_injective d N a mass ha hmass)).apply_symm_apply g

@[simp] theorem latticeMassResolvent_massOperator
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (g : FinLatticeField d N) :
    latticeMassResolvent d N a mass ha hmass (massOperator d N a mass g) = g := by
  exact (LinearEquiv.ofInjectiveEndo (massOperator d N a mass).toLinearMap
    (latticeMassOperator_injective d N a mass ha hmass)).symm_apply_apply g

/-- Any explicitly constructed solution of the mass equation equals the
resolvent. This is the uniqueness seam for the complex Fourier construction. -/
theorem eq_latticeMassResolvent_of_massOperator_eq
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (u g : FinLatticeField d N)
    (hu : massOperator d N a mass u = g) :
    u = latticeMassResolvent d N a mass ha hmass g := by
  apply latticeMassOperator_injective d N a mass ha hmass
  rw [hu, massOperator_latticeMassResolvent]

/-- Exact cancellation of the mass operator against the existing GJ spectral
covariance, proved in its original real eigenbasis. -/
theorem latticeCovarianceGJ_inner_massOperator_right
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f g : FinLatticeField d N) :
    @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
      (latticeCovarianceGJ d N a mass ha hmass f)
      (latticeCovarianceGJ d N a mass ha hmass (massOperator d N a mass g)) =
      (a ^ d : ℝ)⁻¹ * ∑ x : FinLatticeSites d N, f x * g x := by
  rw [latticeCovarianceGJ_inner, latticeCovariance_inner]
  congr 1
  rw [← massEigenbasis_sum_mul_sum_eq_site_inner d N a mass f g]
  apply Finset.sum_congr rfl
  intro k hk
  rw [massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff]
  have hn := ne_of_gt (massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k)
  field_simp [hn]

/-- The actual GJ covariance factor induces the inverse-mass bilinear form
with the physical GJ normalization a^(-d). -/
theorem latticeCovarianceGJ_inner_eq_massResolvent
    (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f g : FinLatticeField d N) :
    @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
      (latticeCovarianceGJ d N a mass ha hmass f)
      (latticeCovarianceGJ d N a mass ha hmass g) =
      (a ^ d : ℝ)⁻¹ * ∑ x : FinLatticeSites d N,
        f x * latticeMassResolvent d N a mass ha hmass g x := by
  simpa only [massOperator_latticeMassResolvent] using
    latticeCovarianceGJ_inner_massOperator_right d N a mass ha hmass f
      (latticeMassResolvent d N a mass ha hmass g)

end Pphi2Clean.Continuum
