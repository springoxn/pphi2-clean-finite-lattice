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

end Pphi2Clean.Continuum
