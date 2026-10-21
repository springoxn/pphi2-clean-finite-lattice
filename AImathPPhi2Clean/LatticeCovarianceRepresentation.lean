import AImathPPhi2Clean.ConcreteGaussianMoment
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
namespace Pphi2Clean.Continuum
open Pphi2Clean.UpstreamLattice

/-- The finite coefficient inclusion used by the upstream ℓ² realization. -/
def finiteCoefficientInclusion {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) : lp (fun _ : ℕ => ℝ) 2 :=
  ∑ k : ι, v k • lp.single 2 ((Fintype.equivFin ι) k).val (1 : ℝ)

/-- Change from physical-site coordinates to the upstream spectral coordinates. -/
def spectralCoefficientEmbedding {ι : Type*} [Fintype ι]
    (D : SpectralCovarianceData ι) (v : EuclideanSpace ℝ ι) :
    lp (fun _ : ℕ => ℝ) 2 :=
  finiteCoefficientInclusion (D.eigenbasis.repr v)

theorem spectralCovariance_repr {ι : Type*} [Fintype ι]
    (D : SpectralCovarianceData ι) (f : ι → ℝ) (k : ι) :
    D.eigenbasis.repr (spectralCovariance D f) k =
      (Real.sqrt (D.eigenvalues k))⁻¹ *
        ∑ x : ι, (D.eigenbasis k : EuclideanSpace ℝ ι) x * f x := by
  classical
  simp [spectralCovariance, map_sum, D.eigenbasis.repr_self, Pi.single_apply]

/-- The migrated finite-Hilbert-space covariance has exactly the upstream
zero-extended ℓ² coefficient formula after the change of orthonormal basis. -/
theorem spectralCoefficientEmbedding_covariance {ι : Type*} [Fintype ι]
    (D : SpectralCovarianceData ι) (f : ι → ℝ) :
    spectralCoefficientEmbedding D (spectralCovariance D f) =
      ∑ k : ι,
        ((Real.sqrt (D.eigenvalues k))⁻¹ *
          ∑ x : ι, (D.eigenbasis k : EuclideanSpace ℝ ι) x * f x) •
          lp.single 2 ((Fintype.equivFin ι) k).val (1 : ℝ) := by
  unfold spectralCoefficientEmbedding finiteCoefficientInclusion
  simp_rw [spectralCovariance_repr]

theorem finiteCoefficientInclusion_inner {ι : Type*} [Fintype ι]
    (v w : EuclideanSpace ℝ ι) :
    @inner ℝ (lp (fun _ : ℕ => ℝ) 2) _
      (finiteCoefficientInclusion v) (finiteCoefficientInclusion w) =
      @inner ℝ (EuclideanSpace ℝ ι) _ v w := by
  classical
  have ho : Orthonormal ℝ (fun k : ι =>
      lp.single (E := fun _ : ℕ => ℝ) 2 ((Fintype.equivFin ι) k).val (1 : ℝ)) := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases h : i = j
    · subst j; simp
    · have hv : ((Fintype.equivFin ι) i).val ≠ ((Fintype.equivFin ι) j).val := by
        intro hij
        exact h ((Fintype.equivFin ι).injective (Fin.ext hij))
      simp [lp.inner_single_left, lp.single_apply, h, hv]
  unfold finiteCoefficientInclusion
  rw [ho.inner_sum (fun k => v k) (fun k => w k) Finset.univ]
  simp [PiLp.inner_apply, mul_comm]

theorem spectralCoefficientEmbedding_inner {ι : Type*} [Fintype ι]
    (D : SpectralCovarianceData ι) (v w : EuclideanSpace ℝ ι) :
    @inner ℝ (lp (fun _ : ℕ => ℝ) 2) _
      (spectralCoefficientEmbedding D v) (spectralCoefficientEmbedding D w) =
      @inner ℝ (EuclideanSpace ℝ ι) _ v w := by
  rw [spectralCoefficientEmbedding, spectralCoefficientEmbedding,
    finiteCoefficientInclusion_inner, D.eigenbasis.repr.inner_map_map]

/-- The GJ scalar commutes with the finite-site-to-spectral-coordinate change. -/
theorem latticeCovarianceGJ_upstream_coefficients
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeSites d N → ℝ) :
    spectralCoefficientEmbedding (spectralData d N a mass ha hmass)
        (latticeCovarianceGJ d N a mass ha hmass f) =
      (Real.sqrt (a^d))⁻¹ •
        ∑ k : FinLatticeSites d N,
          ((Real.sqrt (massEigenvalues d N a mass k))⁻¹ *
            ∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) •
            lp.single 2 ((Fintype.equivFin (FinLatticeSites d N)) k).val (1 : ℝ) := by
  unfold latticeCovarianceGJ spectralCovarianceGJ spectralCoefficientEmbedding
  simp only [ContinuousLinearMap.smul_apply, map_smul]
  unfold finiteCoefficientInclusion
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [spectralCovariance_repr, smul_smul]
  rfl

end Pphi2Clean.Continuum
