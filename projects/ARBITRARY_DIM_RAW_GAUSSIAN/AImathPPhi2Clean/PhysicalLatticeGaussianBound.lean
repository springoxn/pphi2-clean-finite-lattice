import AImathPPhi2Clean.NumberedLatticeGaussianMoment

noncomputable section
namespace Pphi2Clean.Continuum
open Pphi2Clean.UpstreamLattice MeasureTheory ProbabilityTheory

/-- Physical sampling convention: coordinates are representatives in `[0,N)`
and the Riemann weight `a^d` is included in the test vector. -/
def physicalLatticeSample (d N : ℕ) [NeZero N] (a : ℝ)
    (f : FinLatticeSites d N → ℝ) (x : FinLatticeSites d N) : ℝ :=
  a ^ d * f x

/-- The squared discrete test-function seminorm, including cell volume. -/
def latticeTestSeminormSq (d N : ℕ) [NeZero N] (a : ℝ)
    (f : FinLatticeSites d N → ℝ) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N, (f x) ^ 2

theorem massOperator_quadratic_lower (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    mass ^ 2 * ∑ x, f x ^ 2 ≤ ∑ x, f x * (massOperator d N a mass f) x := by
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  have split : ∀ x : FinLatticeSites d N,
      f x * (-(finiteLaplacian d N a f) x + mass ^ 2 * f x) =
      -(f x * (finiteLaplacian d N a f) x) + mass ^ 2 * f x ^ 2 := by
    intro x
    ring
  simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_neg_distrib]
  have hneg := finiteLaplacian_neg_semidefinite d N a ha f
  linarith

theorem massOperatorMatrix_eigenvalues_ge_mass_sq (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    mass ^ 2 ≤ massEigenvalues d N a mass k := by
  let e : FinLatticeField d N := massEigenvectorBasis d N a mass k
  have hev : massOperator d N a mass e = massEigenvalues d N a mass k • e := by
    ext x
    rw [massOperator_eq_matrix_mulVec]
    simpa [e, massEigenvalues, massEigenvectorBasis] using
      congrFun (Matrix.IsHermitian.mulVec_eigenvectorBasis
        (hA := massOperatorMatrix_isHermitian d N a mass) k) x
  have hnorm : ∑ x : FinLatticeSites d N, e x ^ 2 = 1 := by
    have ho := (massEigenvectorBasis d N a mass).orthonormal
    have hn := ho.norm_eq_one k
    have hsq : ‖massEigenvectorBasis d N a mass k‖ ^ 2 = 1 := by
      rw [hn]
      norm_num
    rw [PiLp.norm_sq_eq_of_L2] at hsq
    simpa [Real.norm_eq_abs, sq_abs, e] using hsq
  have hquad := massOperator_quadratic_lower d N a mass ha hmass e
  rw [hev] at hquad
  simp only [Pi.smul_apply, smul_eq_mul] at hquad
  have hdot : ∑ x : FinLatticeSites d N, e x * (massEigenvalues d N a mass k * e x) =
      massEigenvalues d N a mass k := by
    calc
      _ = massEigenvalues d N a mass k * ∑ x, e x ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by rw [hnorm]; ring
  rw [hdot, hnorm] at hquad
  simpa [e] using hquad

/-- The actual GJ covariance of the physically sampled test field. -/
theorem latticeCovarianceGJ_sampled_second_moment_le
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeSites d N → ℝ) :
    @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
      (latticeCovarianceGJ d N a mass ha hmass
        (physicalLatticeSample d N a f))
      (latticeCovarianceGJ d N a mass ha hmass
        (physicalLatticeSample d N a f)) ≤
      mass⁻¹ ^ 2 * latticeTestSeminormSq d N a f := by
  rw [latticeCovarianceGJ_inner, latticeCovariance_inner]
  unfold physicalLatticeSample latticeTestSeminormSq
  have hspec : ∀ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ ≤ mass⁻¹ ^ 2 := by
    intro k
    have hLower := massOperatorMatrix_eigenvalues_ge_mass_sq d N a mass ha hmass k
    have hm2 : 0 < mass ^ 2 := sq_pos_of_pos hmass
    have hLowerpos := massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k
    calc
      (massEigenvalues d N a mass k)⁻¹ ≤ (mass ^ 2)⁻¹ := by
        exact (inv_le_inv₀ hLowerpos hm2).2 hLower
      _ = mass⁻¹ ^ 2 := by
        field_simp
  let u : FinLatticeSites d N → ℝ := f
  have hterm : ∀ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
        (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          (a ^ d * u x)) *
        (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          (a ^ d * u x)) ≤
      mass⁻¹ ^ 2 *
        ((∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          (a ^ d * u x)) *
         (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          (a ^ d * u x))) := by
    intro k
    let A : ℝ := ∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
      (a ^ d * u x)
    change (massEigenvalues d N a mass k)⁻¹ * A * A ≤ mass⁻¹ ^ 2 * (A * A)
    calc
      _ = (massEigenvalues d N a mass k)⁻¹ * (A * A) := by ring
      _ ≤ mass⁻¹ ^ 2 * (A * A) := by
        apply mul_le_mul_of_nonneg_right (hspec k)
        nlinarith [sq_nonneg A]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k hk => hterm k)
  have hparseval := massEigenbasis_sum_mul_sum_eq_site_inner d N a mass
    (fun x => a ^ d * u x) (fun x => a ^ d * u x)
  have ha0 : (a : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos ha d)
  have hscale :
      ∑ x : FinLatticeSites d N,
        (a ^ d * u x) * (a ^ d * u x) =
      (a ^ d) ^ 2 * ∑ x : FinLatticeSites d N, u x ^ 2 := by
    calc
      _ = ∑ x : FinLatticeSites d N, (a ^ d) ^ 2 * u x ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (a ^ d) ^ 2 * ∑ x : FinLatticeSites d N, u x ^ 2 := by
        rw [Finset.mul_sum]
  calc
    (a ^ d : ℝ)⁻¹ *
      ∑ k : FinLatticeSites d N,
        (massEigenvalues d N a mass k)⁻¹ *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
            (a ^ d * u x)) *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
            (a ^ d * u x))
        ≤ (a ^ d : ℝ)⁻¹ *
          (mass⁻¹ ^ 2 * ∑ k : FinLatticeSites d N,
            ((∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
              (a ^ d * u x)) *
             (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
              (a ^ d * u x)))) := by
      have hsum' :
          ∑ k : FinLatticeSites d N,
            (massEigenvalues d N a mass k)⁻¹ *
              (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                (a ^ d * u x)) *
              (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                (a ^ d * u x)) ≤
          mass⁻¹ ^ 2 * ∑ k : FinLatticeSites d N,
            ((∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
              (a ^ d * u x)) *
             (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
              (a ^ d * u x))) := by
        calc
          _ ≤ ∑ k : FinLatticeSites d N,
              mass⁻¹ ^ 2 *
                ((∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                  (a ^ d * u x)) *
                 (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                  (a ^ d * u x))) := hsum
          _ = mass⁻¹ ^ 2 * ∑ k : FinLatticeSites d N,
                ((∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                  (a ^ d * u x)) *
                 (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                  (a ^ d * u x))) := by rw [Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum'
        (inv_nonneg.mpr (le_of_lt (pow_pos ha d)))
    _ = mass⁻¹ ^ 2 * (a ^ d * ∑ x : FinLatticeSites d N, u x ^ 2) := by
          rw [hparseval, hscale]
          field_simp [ha0]
    _ = mass⁻¹ ^ 2 * latticeTestSeminormSq d N a f := by rfl

noncomputable def physicalCoordinateEval (d N : ℕ) [NeZero N] (a : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites d N))) :
    EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N))) →L[ℝ] ℝ :=
  (a ^ d) • EuclideanSpace.proj j

/-- Second moment of the actual numbered GJ Gaussian pushforward for physically
weighted coordinate sampling, bounded by the discrete test seminorm. -/
theorem numberedLatticeGJ_physical_second_moment_le
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) :
    ∫ ω : WeakDual ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))),
        (ω f) ^ 2
      ∂(finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ d N a mass ha hmass)).map
        (latticeEmbedLift (physicalCoordinateEval d N a)) ≤
      mass⁻¹ ^ 2 * latticeTestSeminormSq d N a
        (fun x => f ((Fintype.equivFin (FinLatticeSites d N)) x)) := by
  have hcov := latticeCovarianceGJ_sampled_second_moment_le d N a mass ha hmass
    (fun x => f ((Fintype.equivFin (FinLatticeSites d N)) x))
  rw [latticeCovarianceGJ_inner, latticeCovariance_inner] at hcov
  rw [numberedLatticeCovarianceGJ_lift_second_moment]
  simpa [physicalCoordinateEval, physicalLatticeSample, latticeTestSeminormSq,
    pow_two, mul_assoc] using hcov

end Pphi2Clean.Continuum
