import AImathPPhi2Clean.LatticeGaussianContinuumConsumer

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory

/-- General finite-site version of the lattice-to-configuration lift.  The
caller chooses the actual finite site type, so the construction can use
`Fin d → ZMod N` without identifying it with `Fin n`. -/
def finiteSiteEmbedLift
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (eval : ι → E →L[ℝ] ℝ)
    (ω : WeakDual ℝ (ι → ℝ)) : WeakDual ℝ E :=
  (∑ x : ι, (ω (Pi.single x (1 : ℝ))) • eval x : E →L[ℝ] ℝ)

@[simp] theorem finiteSiteEmbedLift_eval
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (eval : ι → E →L[ℝ] ℝ)
    (ω : WeakDual ℝ (ι → ℝ)) (f : E) :
    finiteSiteEmbedLift eval ω f =
      ∑ x : ι, ω (Pi.single x (1 : ℝ)) * eval x f := by
  unfold finiteSiteEmbedLift
  change (∑ x : ι, (ω (Pi.single x (1 : ℝ))) • eval x) f = _
  rw [ContinuousLinearMap.sum_apply]
  simp [smul_eq_mul]

/-- Finite-dimensional spectral covariance data.  This is the exact
`Q^(-1/2)` construction used by the upstream lattice covariance, with the
finite-site eigenbasis and positive eigenvalues exposed as data so the
construction is independent of any continuum theorem. -/
structure SpectralCovarianceData (ι : Type*) [Fintype ι] where
  eigenbasis : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)
  eigenvalues : ι → ℝ
  eigenvalues_pos : ∀ k, 0 < eigenvalues k

/-- Spectral `Q^(-1/2)` CLM into the finite Hilbert space. -/
noncomputable def spectralCovariance
    {ι : Type*} [Fintype ι]
    (D : SpectralCovarianceData ι) :
    (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι := by
  let L : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
    { toFun := fun f =>
        ∑ k : ι,
          ((Real.sqrt (D.eigenvalues k))⁻¹ *
            ∑ x : ι, (D.eigenbasis k : EuclideanSpace ℝ ι) x * f x) •
            (D.eigenbasis k : EuclideanSpace ℝ ι)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro r f
        ext j
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.sum_apply]
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] }
  exact { L with cont := L.continuous_of_finiteDimensional }

/-- Spectral covariance bilinear identity. -/
theorem spectralCovariance_inner
    {ι : Type*} [Fintype ι]
    (D : SpectralCovarianceData ι) (f g : ι → ℝ) :
    @inner ℝ (EuclideanSpace ℝ ι) _ (spectralCovariance D f)
      (spectralCovariance D g) =
      ∑ k : ι, (D.eigenvalues k)⁻¹ *
        (∑ x : ι, (D.eigenbasis k : EuclideanSpace ℝ ι) x * f x) *
        (∑ x : ι, (D.eigenbasis k : EuclideanSpace ℝ ι) x * g x) := by
  let cf : ι → ℝ := fun k =>
    (Real.sqrt (D.eigenvalues k))⁻¹ *
      ∑ x : ι, (D.eigenbasis k : EuclideanSpace ℝ ι) x * f x
  let cg : ι → ℝ := fun k =>
    (Real.sqrt (D.eigenvalues k))⁻¹ *
      ∑ x : ι, (D.eigenbasis k : EuclideanSpace ℝ ι) x * g x
  have hinner := D.eigenbasis.orthonormal.inner_sum cf cg (Finset.univ : Finset ι)
  change @inner ℝ (EuclideanSpace ℝ ι) _
      (∑ k : ι, cf k • (D.eigenbasis k : EuclideanSpace ℝ ι))
      (∑ k : ι, cg k • (D.eigenbasis k : EuclideanSpace ℝ ι)) = _
  rw [hinner]
  simp only [cf, cg]
  apply Finset.sum_congr rfl
  intro k hk
  have hs : Real.sqrt (D.eigenvalues k) * Real.sqrt (D.eigenvalues k) =
      D.eigenvalues k := Real.mul_self_sqrt (le_of_lt (D.eigenvalues_pos k))
  rw [map_mul]
  simp only [starRingEnd_apply, star_trivial]
  have hpos : 0 < D.eigenvalues k := D.eigenvalues_pos k
  have hsqrt : Real.sqrt (D.eigenvalues k) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hpos
  field_simp [hsqrt, ne_of_gt hpos]
  have hs' : (Real.sqrt (D.eigenvalues k)) ^ 2 = D.eigenvalues k := by
    nlinarith [hs]
  rw [hs']
  ring


/-- GJ-normalized spectral covariance. -/
noncomputable def spectralCovarianceGJ
    {ι : Type*} [Fintype ι]
    (a : ℝ) (d : ℕ) (ha : 0 < a) (D : SpectralCovarianceData ι) :
    (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
  (Real.sqrt (a ^ d))⁻¹ • spectralCovariance D

theorem spectralCovarianceGJ_inner
    {ι : Type*} [Fintype ι]
    (a : ℝ) (d : ℕ) (ha : 0 < a) (D : SpectralCovarianceData ι)
    (f g : ι → ℝ) :
    @inner ℝ (EuclideanSpace ℝ ι) _ (spectralCovarianceGJ a d ha D f)
      (spectralCovarianceGJ a d ha D g) =
      (a ^ d : ℝ)⁻¹ *
        @inner ℝ (EuclideanSpace ℝ ι) _ (spectralCovariance D f)
          (spectralCovariance D g) := by
  unfold spectralCovarianceGJ
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
  have hp : 0 < (a : ℝ) ^ d := pow_pos ha _
  have hs : Real.sqrt (a ^ d) * Real.sqrt (a ^ d) = a ^ d :=
    Real.mul_self_sqrt (le_of_lt hp)
  simp
  rw [show (Real.sqrt (a ^ d))⁻¹ *
      ((Real.sqrt (a ^ d))⁻¹ *
        @inner ℝ (EuclideanSpace ℝ ι) _ (spectralCovariance D f)
          (spectralCovariance D g)) =
      ((Real.sqrt (a ^ d))⁻¹ * (Real.sqrt (a ^ d))⁻¹) *
        @inner ℝ (EuclideanSpace ℝ ι) _ (spectralCovariance D f)
          (spectralCovariance D g) by ring]
  congr 1
  rw [show (Real.sqrt (a ^ d))⁻¹ * (Real.sqrt (a ^ d))⁻¹ =
      (Real.sqrt (a ^ d) * Real.sqrt (a ^ d))⁻¹ by rw [mul_inv]]
  rw [hs]

end Pphi2Clean.Continuum
