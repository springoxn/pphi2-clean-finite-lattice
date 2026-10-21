import AImathPPhi2Clean.ConcreteGaussianMoment

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

/-- Transport a finite covariance factor along an explicit numbering of sites.
Both its test-field input and Hilbert output are transported. -/
def reindexCovariance {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) :
    (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) := by
  let L : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun f => WithLp.toLp 2 (fun k => (T (fun x => f (e x))) (e.symm k))
      map_add' := by
        intro f g
        ext k
        change (T ((fun x => f (e x)) + (fun x => g (e x)))) (e.symm k) = _
        rw [map_add]
        rfl
      map_smul' := by
        intro r f
        ext k
        change (T (r • (fun x => f (e x)))) (e.symm k) = _
        rw [map_smul]
        rfl }
  exact { L with cont := L.continuous_of_finiteDimensional }

theorem reindexCovariance_inner {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι)
    (f g : Fin n → ℝ) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (reindexCovariance e T f) (reindexCovariance e T g) =
      @inner ℝ (EuclideanSpace ℝ ι) _ (T (fun x => f (e x))) (T (fun x => g (e x))) := by
  simp only [PiLp.inner_apply, reindexCovariance]
  exact e.symm.sum_comp (fun x => inner ℝ ((T (fun y => f (e y))) x) ((T (fun y => g (e y))) x))

/-- The actual periodic GJ factor on the original `Fin n` clean interface. -/
def numberedLatticeCovarianceGJ (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (Fin (Fintype.card (FinLatticeSites d N)) → ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N))) :=
  reindexCovariance (Fintype.equivFin (FinLatticeSites d N))
    (latticeCovarianceGJ d N a mass ha hmass)

/-- Exact GJ spectral second moment for the original clean `latticeEmbedLift`,
under the actual finite Gaussian probability law with numbered periodic sites. -/
theorem numberedLatticeCovarianceGJ_lift_second_moment
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (eval : Fin (Fintype.card (FinLatticeSites d N)) → E →L[ℝ] ℝ) (f : E) :
    ∫ ω : WeakDual ℝ E, (ω f)^2
      ∂(finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ d N a mass ha hmass)).map
        (latticeEmbedLift eval) =
      (a^d : ℝ)⁻¹ * ∑ k : FinLatticeSites d N,
        (massEigenvalues d N a mass k)⁻¹ *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
            eval ((Fintype.equivFin (FinLatticeSites d N)) x) f)^2 := by
  rw [latticeEmbedLift_pushforward_second_moment, numberedLatticeCovarianceGJ,
    reindexCovariance_inner, latticeCovarianceGJ_inner, latticeCovariance_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [latticeTestField]
  ring

end Pphi2Clean.Continuum
