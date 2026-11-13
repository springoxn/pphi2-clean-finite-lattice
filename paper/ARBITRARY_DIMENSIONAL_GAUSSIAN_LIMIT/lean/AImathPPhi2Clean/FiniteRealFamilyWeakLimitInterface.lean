import AImathPPhi2Clean.FiniteRealFamilyVarianceIdentity
import AImathPPhi2Clean.PeriodicTorusResolventLimit

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice
open scoped MatrixOrder

/-- The actual fixed-volume family converges once the target finite-dimensional Gaussian
    law and its covariance quadratic form are supplied explicitly. -/
theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_target
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ → BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g)))
    (μ₀ : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
    (hμ₀ : HasGaussianLaw id (μ₀ : Measure (EuclideanSpace ℝ (Fin m))))
    (hmean₀ : ∀ t : EuclideanSpace ℝ (Fin m), ∫ x, inner ℝ t x ∂μ₀ = 0)
    (hquad₀ : ∀ t : EuclideanSpace ℝ (Fin m),
      Var[fun x => inner ℝ t x; (μ₀ : Measure (EuclideanSpace ℝ (Fin m)))] =
        ∑ i : Fin m, ∑ j : Fin m, t i * t j * C (fs i) (fs j)) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop (nhds μ₀) := by
  let μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) := fun n =>
    let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs
  have hμ : ∀ n, HasGaussianLaw id (μ n : Measure (EuclideanSpace ℝ (Fin m))) := by
    intro n; dsimp [μ]; let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    exact (physicalFamilyEvalMeasure_hasGaussianLaw d N m (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs).isGaussian_map.hasGaussianLaw_id
  have hmean : ∀ t : EuclideanSpace ℝ (Fin m), Filter.Tendsto
      (fun n => ∫ x, inner ℝ t x ∂(μ n)) Filter.atTop (nhds (∫ x, inner ℝ t x ∂μ₀)) := by
    intro t
    have hzero : (fun n => ∫ x, inner ℝ t x ∂(μ n)) = fun _ => 0 := by
      funext n; dsimp [μ]; let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
      exact physicalFamilyEvalMeasure_projectedMean_zero d N m (L / (N : ℝ)) mass
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs t
    rw [hzero, hmean₀ t]; exact tendsto_const_nhds
  let Cmat : Fin m → Fin m → ℝ := fun i j => C (fs i) (fs j)
  let Cn : ℕ → Fin m → Fin m → ℝ := fun n i j =>
    let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ), ω (fs i) * ω (fs j) ∂physicalGJMeasure d N (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
  have hcov : ∀ i j, Filter.Tendsto (fun n => Cn n i j) Filter.atTop (nhds (Cmat i j)) := by
    intro i j
    simpa [Cmat, Cn] using
      (physicalGJMeasure_covariance_tendsto_of_inner_tendsto (Filter.atTop) d (fun n => n + 1)
        (fun n => ⟨Nat.succ_ne_zero n⟩) (fun n => L / ((n + 1 : ℕ) : ℝ))
        (fun n => div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) mass hmass C hinner (fs i) (fs j))
  have hquad : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin m)),
      Var[fun x => inner ℝ t x; (μ n : Measure (EuclideanSpace ℝ (Fin m)))] =
        ∑ i : Fin m, ∑ j : Fin m, t i * t j * Cn n i j := by
    intro n t; dsimp [μ, Cn]; let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    change Var[fun x => inner ℝ t x; physicalFamilyEvalMeasure d N m (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs] = _
    simpa [Cn, N] using (physicalFamilyEvalMeasure_projectedVariance_eq_covariance_quadratic d N m
      (L / (N : ℝ)) mass (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs t)
  have hquad₀' : ∀ t : EuclideanSpace ℝ (Fin m),
      Var[fun x => inner ℝ t x; (μ₀ : Measure (EuclideanSpace ℝ (Fin m)))] =
        ∑ i : Fin m, ∑ j : Fin m, t i * t j * Cmat i j := by
    intro t; simpa [Cmat] using hquad₀ t
  exact finiteGaussian_weak_tendsto_of_covariance_entries μ μ₀ hμ hμ₀ hmean Cmat Cn hcov hquad hquad₀'

theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_target_indexed
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ → BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ i j : Fin m, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) (fs i)))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) (fs j))))
      Filter.atTop (nhds (C (fs i) (fs j))))
    (μ₀ : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
    (hμ₀ : HasGaussianLaw id (μ₀ : Measure (EuclideanSpace ℝ (Fin m))))
    (hmean₀ : ∀ t : EuclideanSpace ℝ (Fin m), ∫ x, inner ℝ t x ∂μ₀ = 0)
    (hquad₀ : ∀ t : EuclideanSpace ℝ (Fin m),
      Var[fun x => inner ℝ t x; (μ₀ : Measure (EuclideanSpace ℝ (Fin m)))] =
        ∑ i : Fin m, ∑ j : Fin m, t i * t j * C (fs i) (fs j)) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop (nhds μ₀) := by
  let μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) := fun n =>
    let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs
  have hμ : ∀ n, HasGaussianLaw id (μ n : Measure (EuclideanSpace ℝ (Fin m))) := by
    intro n
    dsimp [μ]
    let N := n + 1
    letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    exact (physicalFamilyEvalMeasure_hasGaussianLaw d N m (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs).isGaussian_map.hasGaussianLaw_id
  have hmean : ∀ t : EuclideanSpace ℝ (Fin m), Filter.Tendsto
      (fun n => ∫ x, inner ℝ t x ∂(μ n)) Filter.atTop (nhds (∫ x, inner ℝ t x ∂μ₀)) := by
    intro t
    have hzero : (fun n => ∫ x, inner ℝ t x ∂(μ n)) = fun _ => 0 := by
      funext n
      dsimp [μ]
      let N := n + 1
      letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
      exact physicalFamilyEvalMeasure_projectedMean_zero d N m (L / (N : ℝ)) mass
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs t
    rw [hzero, hmean₀ t]
    exact tendsto_const_nhds
  let Cmat : Fin m → Fin m → ℝ := fun i j => C (fs i) (fs j)
  let Cn : ℕ → Fin m → Fin m → ℝ := fun n i j =>
    let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
      ω (fs i) * ω (fs j) ∂physicalGJMeasure d N (L / (N : ℝ)) mass
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
  have hcov : ∀ i j, Filter.Tendsto (fun n => Cn n i j) Filter.atTop (nhds (Cmat i j)) := by
    intro i j
    have hEq : (fun n => Cn n i j) = fun n =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) (fs i)))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) (fs j))) := by
      funext n
      dsimp [Cn]
      let N := n + 1
      letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
      exact physicalGJMeasure_mixedMoment d N (L / (N : ℝ)) mass
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass (fs i) (fs j)
    rw [hEq]
    simpa [Cmat] using hinner i j
  have hquad : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin m)),
      Var[fun x => inner ℝ t x; (μ n : Measure (EuclideanSpace ℝ (Fin m)))] =
        ∑ i : Fin m, ∑ j : Fin m, t i * t j * Cn n i j := by
    intro n t
    dsimp [μ, Cn]
    let N := n + 1
    letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    change Var[fun x => inner ℝ t x; physicalFamilyEvalMeasure d N m (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs] = _
    simpa [Cn, N] using (physicalFamilyEvalMeasure_projectedVariance_eq_covariance_quadratic d N m
      (L / (N : ℝ)) mass (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs t)
  have hquad₀' : ∀ t : EuclideanSpace ℝ (Fin m),
      Var[fun x => inner ℝ t x; (μ₀ : Measure (EuclideanSpace ℝ (Fin m)))] =
        ∑ i : Fin m, ∑ j : Fin m, t i * t j * Cmat i j := by
    intro t
    simpa [Cmat] using hquad₀ t
  exact finiteGaussian_weak_tendsto_of_covariance_entries μ μ₀ hμ hμ₀ hmean Cmat Cn hcov hquad hquad₀'

def targetCoordinateFamily (m : ℕ) : Fin m → (Fin m → ℝ) := fun i => Pi.single i 1

def targetCoordinateMap {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) : WeakDual ℝ (Fin m → ℝ) → EuclideanSpace ℝ (Fin m) :=
  fun ω => WithLp.toLp 2 (fun i => ω (targetCoordinateFamily m i))

def targetCoordinateMeasure {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) : Measure (EuclideanSpace ℝ (Fin m)) :=
  Measure.map (targetCoordinateMap T) (finiteCovarianceGaussianMeasure T)

instance targetCoordinateMeasure_probability {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) : IsProbabilityMeasure (targetCoordinateMeasure T) := by
  unfold targetCoordinateMeasure targetCoordinateMap
  apply map_preserves_probability
  exact (finiteCovarianceGaussianMeasure_family_hasGaussianLaw T (targetCoordinateFamily m)).aemeasurable

def targetCoordinateProbabilityMeasure {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) :=
  ⟨targetCoordinateMeasure T, inferInstance⟩

theorem targetCoordinateMeasure_hasGaussianLaw {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) : HasGaussianLaw id (targetCoordinateMeasure T) := by
  exact (finiteCovarianceGaussianMeasure_family_hasGaussianLaw T (targetCoordinateFamily m)).isGaussian_map.hasGaussianLaw_id

theorem targetCoordinateMeasure_covariance_entry {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) (i j : Fin m) :
    ∫ z : EuclideanSpace ℝ (Fin m), z i * z j ∂targetCoordinateMeasure T =
      @inner ℝ (EuclideanSpace ℝ (Fin m)) _ (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) := by
  unfold targetCoordinateMeasure targetCoordinateMap
  have hmeas : Measurable (fun z : EuclideanSpace ℝ (Fin m) => z i * z j) := by fun_prop
  rw [integral_map (finiteCovarianceGaussianMeasure_family_hasGaussianLaw T (targetCoordinateFamily m)).aemeasurable hmeas.aestronglyMeasurable]
  exact finiteCovarianceGaussianMeasure_covariance T (targetCoordinateFamily m i) (targetCoordinateFamily m j)

theorem targetCoordinateMeasure_covariance_factor_matches {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) (Cmat : Fin m → Fin m → ℝ)
    (hfactor : ∀ i j, @inner ℝ (EuclideanSpace ℝ (Fin m)) _ (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) = Cmat i j) :
    ∀ i j, ∫ z : EuclideanSpace ℝ (Fin m), z i * z j ∂targetCoordinateMeasure T = Cmat i j := by
  intro i j
  rw [targetCoordinateMeasure_covariance_entry T i j, hfactor i j]

theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_coordinate_target
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ → BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g)))
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hmean₀ : ∀ t : EuclideanSpace ℝ (Fin m), ∫ x, inner ℝ t x ∂targetCoordinateMeasure T = 0)
    (hquad₀ : ∀ t : EuclideanSpace ℝ (Fin m), Var[fun x => inner ℝ t x; targetCoordinateMeasure T] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j * C (fs i) (fs j)) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop (nhds (targetCoordinateProbabilityMeasure T)) := by
  exact physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_target
    (d := d) (m := m) (L := L) (mass := mass) (hL := hL) (hmass := hmass)
    (fs := fs) (C := C) (hinner := hinner)
    (μ₀ := targetCoordinateProbabilityMeasure T)
    (hμ₀ := targetCoordinateMeasure_hasGaussianLaw T)
    (hmean₀ := hmean₀) (hquad₀ := hquad₀)

def periodicResolventCovarianceMatrix
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) : Fin m → Fin m → ℝ :=
  fun i j => (physicalTorusResolventPairing d L mass hmass (fs i) (fs j)).re

def PeriodicResolventCovarianceFactorization
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) : Prop :=
  ∃ T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m),
    ∀ i j, @inner ℝ (EuclideanSpace ℝ (Fin m)) _
      (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) =
        periodicResolventCovarianceMatrix d m L mass hmass fs i j

/-- A finite real positive-semidefinite matrix has a concrete Gram factor. -/
theorem finiteRealMatrix_factorization_of_posSemidef
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : Matrix.PosSemidef A) :
    ∃ T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m),
      ∀ i j, @inner ℝ (EuclideanSpace ℝ (Fin m)) _
        (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) = A i j := by
  let B : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt A
  have hBsq : B * B = A := by
    simpa [B, pow_two] using (CFC.sq_sqrt A hA.nonneg)
  have hBherm : B.IsHermitian := by
    simpa [B] using (CFC.sqrt_nonneg A).1
  let M : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.mk (Matrix.mulVecLin B)
      (LinearMap.continuous_of_finiteDimensional (Matrix.mulVecLin B))
  let T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp M
  refine ⟨T, ?_⟩
  intro i j
  change inner ℝ (WithLp.toLp 2 (B.mulVec (Pi.single i 1)))
    (WithLp.toLp 2 (B.mulVec (Pi.single j 1))) = A i j
  rw [B.mulVec_single_one, B.mulVec_single_one]
  simp only [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply]
  simp only [Matrix.col_apply, starRingEnd_apply, star_trivial]
  calc
    (∑ x, B x j * B x i) = ∑ x, B i x * B x j := by
      apply Finset.sum_congr rfl
      intro x hx
      have hsym := congrFun (congrFun hBherm i) x
      simp only [Matrix.conjTranspose_apply, star_trivial] at hsym
      rw [hsym]
      ring
    _ = (B * B) i j := by rw [Matrix.mul_apply]
    _ = A i j := congrFun (congrFun hBsq i) j

/-- The periodic covariance factor is concrete once its matrix PSD is proved. -/
theorem periodicResolventCovarianceFactorization_of_matrix_posSemidef
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hA : Matrix.PosSemidef (periodicResolventCovarianceMatrix d m L mass hmass fs)) :
    PeriodicResolventCovarianceFactorization d m L mass hmass fs := by
  rcases finiteRealMatrix_factorization_of_posSemidef m
      (periodicResolventCovarianceMatrix d m L mass hmass fs) hA with ⟨T, hT⟩
  exact ⟨T, hT⟩

theorem periodicResolventCovarianceMatrix_symmetric_of_pairing_symm
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hpair : ∀ f g, physicalTorusResolventPairing d L mass hmass f g =
      physicalTorusResolventPairing d L mass hmass g f) :
    ∀ i j, periodicResolventCovarianceMatrix d m L mass hmass fs i j =
      periodicResolventCovarianceMatrix d m L mass hmass fs j i := by
  intro i j
  unfold periodicResolventCovarianceMatrix
  rw [hpair (fs i) (fs j)]

theorem periodicResolventCovarianceMatrix_symmetric_of_fourier
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∀ i j, periodicResolventCovarianceMatrix d m L mass hmass fs i j =
      periodicResolventCovarianceMatrix d m L mass hmass fs j i := by
  apply periodicResolventCovarianceMatrix_symmetric_of_pairing_symm
  intro f g
  calc
    physicalTorusResolventPairing d L mass hmass f g =
        torusFourierGreenPairing d L mass f g :=
      (torusFourierGreenPairing_eq_physicalTorusResolventPairing
        d L mass hL hmass f g).symm
    _ = torusFourierGreenPairing d L mass g f :=
      torusFourierGreenPairing_symm d L mass f g
    _ = physicalTorusResolventPairing d L mass hmass g f :=
      torusFourierGreenPairing_eq_physicalTorusResolventPairing
        d L mass hL hmass g f

theorem periodicResolventCovarianceMatrix_symmetric_of_factorization
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hfactor : PeriodicResolventCovarianceFactorization d m L mass hmass fs) :
    ∀ i j, periodicResolventCovarianceMatrix d m L mass hmass fs i j =
      periodicResolventCovarianceMatrix d m L mass hmass fs j i := by
  rcases hfactor with ⟨T, hT⟩
  intro i j
  rw [← hT i j, ← hT j i]
  exact real_inner_comm _ _

def PeriodicResolventCovariancePSD
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) : Prop :=
  ∀ t : EuclideanSpace ℝ (Fin m),
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, t i * t j *
      periodicResolventCovarianceMatrix d m L mass hmass fs i j

/-- Direct Fourier positivity of the periodic resolvent covariance matrix. -/
theorem periodicResolventCovarianceMatrix_nonneg_quadratic_of_fourier
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, t i * t j *
      periodicResolventCovarianceMatrix d m L mass hmass fs i j := by
  have hfour := torusFourierGreenPairing_quadratic_eq_square_tsum
    d m L mass hL hmass (fun i => t i) fs
  have hnon := torusFourierSquareTsum_prefactor_re_nonneg
    d m L mass hL hmass (fun i => t i) fs
  have hpair : (∑ i : Fin m, ∑ j : Fin m,
      (t i : ℂ) * (t j : ℂ) *
        physicalTorusResolventPairing d L mass hmass (fs i) (fs j)) =
      ∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) *
          torusFourierGreenPairing d L mass (fs i) (fs j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [torusFourierGreenPairing_eq_physicalTorusResolventPairing
      d L mass hL hmass (fs i) (fs j)]
  calc
    ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        periodicResolventCovarianceMatrix d m L mass hmass fs i j =
      (∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) *
          physicalTorusResolventPairing d L mass hmass (fs i) (fs j)).re := by
            simp [periodicResolventCovarianceMatrix, Complex.mul_re]
    _ = (∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) *
          torusFourierGreenPairing d L mass (fs i) (fs j)).re := by rw [hpair]
    _ = ((L : ℂ)⁻¹ ^ d * ∑' k : Fin d → ℤ,
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)).re := by rw [← hfour]
    _ ≥ 0 := hnon

theorem periodicResolventCovarianceMatrix_nonneg_quadratic_of_factorization
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hfactor : PeriodicResolventCovarianceFactorization d m L mass hmass fs)
    (t : EuclideanSpace ℝ (Fin m)) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, t i * t j *
      periodicResolventCovarianceMatrix d m L mass hmass fs i j := by
  rcases hfactor with ⟨T, hT⟩
  have hgram : (∑ i : Fin m, ∑ j : Fin m, t i * t j *
      periodicResolventCovarianceMatrix d m L mass hmass fs i j) =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        @inner ℝ (EuclideanSpace ℝ (Fin m)) _
          (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hT i j]
  rw [hgram]
  let v : EuclideanSpace ℝ (Fin m) :=
    ∑ i : Fin m, t i • T (targetCoordinateFamily m i)
  have hv : @inner ℝ (EuclideanSpace ℝ (Fin m)) _ v v =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        @inner ℝ (EuclideanSpace ℝ (Fin m)) _
          (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) := by
    simp only [v, real_inner_comm, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [← hv, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

theorem periodicResolventCovarianceMatrix_psd_of_factorization
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hfactor : PeriodicResolventCovarianceFactorization d m L mass hmass fs) :
    PeriodicResolventCovariancePSD d m L mass hmass fs := by
  intro t
  exact periodicResolventCovarianceMatrix_nonneg_quadratic_of_factorization
    d m L mass hmass fs hfactor t

/-- The periodic covariance matrix is PSD by the complete Fourier square formula. -/
 theorem periodicResolventCovarianceMatrix_matrix_posSemidef_of_fourier
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Matrix.PosSemidef (periodicResolventCovarianceMatrix d m L mass hmass fs) := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · show Matrix.conjTranspose (periodicResolventCovarianceMatrix d m L mass hmass fs :
        Matrix (Fin m) (Fin m) ℝ) =
      (periodicResolventCovarianceMatrix d m L mass hmass fs : Matrix (Fin m) (Fin m) ℝ)
    ext i j
    change star (periodicResolventCovarianceMatrix d m L mass hmass fs j i) =
      periodicResolventCovarianceMatrix d m L mass hmass fs i j
    simp only [star_trivial]
    exact periodicResolventCovarianceMatrix_symmetric_of_fourier d m L mass hL hmass fs j i
  · intro x
    let t : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x
    have h := periodicResolventCovarianceMatrix_nonneg_quadratic_of_fourier
      d m L mass hL hmass fs t
    simpa [dotProduct, Matrix.mulVec, t, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm] using h

theorem periodicResolventCovarianceMatrix_matrix_posSemidef_of_factorization
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hfactor : PeriodicResolventCovarianceFactorization d m L mass hmass fs) :
    Matrix.PosSemidef (periodicResolventCovarianceMatrix d m L mass hmass fs) := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · show Matrix.conjTranspose (periodicResolventCovarianceMatrix d m L mass hmass fs :
      Matrix (Fin m) (Fin m) ℝ) =
      (periodicResolventCovarianceMatrix d m L mass hmass fs : Matrix (Fin m) (Fin m) ℝ)
    ext i j
    change star (periodicResolventCovarianceMatrix d m L mass hmass fs j i) =
      periodicResolventCovarianceMatrix d m L mass hmass fs i j
    simp only [star_trivial]
    exact periodicResolventCovarianceMatrix_symmetric_of_factorization
      d m L mass hmass fs hfactor j i
  · intro x
    let t : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x
    have h := periodicResolventCovarianceMatrix_nonneg_quadratic_of_factorization
      d m L mass hmass fs hfactor t
    simpa [dotProduct, Matrix.mulVec, t, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm] using h

/-- Canonical factor obtained from the positive-semidefinite periodic covariance matrix.
The underlying matrix square root is fixed by `CFC.sqrt`, so this definition does not
make an existential choice of a factor. -/
noncomputable def periodicResolventCovarianceCanonicalFactor
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  let A : Matrix (Fin m) (Fin m) ℝ :=
    periodicResolventCovarianceMatrix d m L mass hmass fs
  let B : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt A
  let M : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.mk (Matrix.mulVecLin B)
      (LinearMap.continuous_of_finiteDimensional (Matrix.mulVecLin B))
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp M

/-- The canonical factor has exactly the periodic Fourier covariance as its Gram matrix. -/
theorem periodicResolventCovarianceCanonicalFactor_gram
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) (i j : Fin m) :
    @inner ℝ (EuclideanSpace ℝ (Fin m)) _
      (periodicResolventCovarianceCanonicalFactor d m L mass hmass fs
        (targetCoordinateFamily m i))
      (periodicResolventCovarianceCanonicalFactor d m L mass hmass fs
        (targetCoordinateFamily m j)) =
      periodicResolventCovarianceMatrix d m L mass hmass fs i j := by
  let A : Matrix (Fin m) (Fin m) ℝ :=
    periodicResolventCovarianceMatrix d m L mass hmass fs
  let B : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt A
  have hA : Matrix.PosSemidef A := by
    simpa [A] using periodicResolventCovarianceMatrix_matrix_posSemidef_of_fourier
      d m L mass hL hmass fs
  have hBsq : B * B = A := by
    simpa [B, pow_two] using (CFC.sq_sqrt A hA.nonneg)
  have hBherm : B.IsHermitian := by
    simpa [B] using (CFC.sqrt_nonneg A).1
  change inner ℝ (WithLp.toLp 2 (B.mulVec (Pi.single i 1)))
    (WithLp.toLp 2 (B.mulVec (Pi.single j 1))) = A i j
  rw [B.mulVec_single_one, B.mulVec_single_one]
  simp only [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply]
  simp only [Matrix.col_apply, starRingEnd_apply, star_trivial]
  calc
    (∑ x, B x j * B x i) = ∑ x, B i x * B x j := by
      apply Finset.sum_congr rfl
      intro x hx
      have hsym := congrFun (congrFun hBherm i) x
      simp only [Matrix.conjTranspose_apply, star_trivial] at hsym
      rw [hsym]
      ring
    _ = (B * B) i j := by rw [Matrix.mul_apply]
    _ = A i j := congrFun (congrFun hBsq i) j
    _ = periodicResolventCovarianceMatrix d m L mass hmass fs i j := rfl

/-- The Fourier PSD theorem supplies the concrete Euclidean Gram factor. -/
theorem periodicResolventCovarianceFactorization_of_fourier
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    PeriodicResolventCovarianceFactorization d m L mass hmass fs := by
  exact periodicResolventCovarianceFactorization_of_matrix_posSemidef
    d m L mass hmass fs
    (periodicResolventCovarianceMatrix_matrix_posSemidef_of_fourier
      d m L mass hL hmass fs)

theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_factor
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ → BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g)))
    (hC : ∀ i j, C (fs i) (fs j) = periodicResolventCovarianceMatrix d m L mass hmass fs i j)
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hfactor : ∀ i j, @inner ℝ (EuclideanSpace ℝ (Fin m)) _
      (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) =
        periodicResolventCovarianceMatrix d m L mass hmass fs i j)
    (hmean₀ : ∀ t : EuclideanSpace ℝ (Fin m),
      ∫ x, inner ℝ t x ∂targetCoordinateMeasure T = 0)
    (hquad₀ : ∀ t : EuclideanSpace ℝ (Fin m), Var[fun x => inner ℝ t x; targetCoordinateMeasure T] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j * C (fs i) (fs j)) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop (nhds (targetCoordinateProbabilityMeasure T)) := by
  exact physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_coordinate_target
    d m L mass hL hmass fs C hinner T hmean₀ hquad₀

theorem targetCoordinateMeasure_mean_zero {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (t : EuclideanSpace ℝ (Fin m)) :
    ∫ z, inner ℝ t z ∂targetCoordinateMeasure T = 0 := by
  unfold targetCoordinateMeasure targetCoordinateMap
  have hmeas : Measurable (fun z : EuclideanSpace ℝ (Fin m) => inner ℝ t z) := by
    fun_prop
  rw [integral_map
    (finiteCovarianceGaussianMeasure_family_hasGaussianLaw T
      (targetCoordinateFamily m)).aemeasurable hmeas.aestronglyMeasurable]
  change ∫ ω : WeakDual ℝ (Fin m → ℝ),
      inner ℝ t (WithLp.toLp 2 (fun i => ω (targetCoordinateFamily m i))) ∂finiteCovarianceGaussianMeasure T = 0
  let P : Measure (WeakDual ℝ (Fin m → ℝ)) := finiteCovarianceGaussianMeasure T
  have hvec_mem : MemLp (fun ω : WeakDual ℝ (Fin m → ℝ) =>
      WithLp.toLp 2 (fun i => ω (targetCoordinateFamily m i))) 2 P :=
    (finiteCovarianceGaussianMeasure_family_hasGaussianLaw T
      (targetCoordinateFamily m)).memLp_two
  have hcoord_mem : ∀ i : Fin m,
      MemLp (fun ω : WeakDual ℝ (Fin m → ℝ) => ω (targetCoordinateFamily m i)) 2 P := by
    intro i
    apply (hvec_mem.norm).mono'
    · have hω : Measurable (fun ω : WeakDual ℝ (Fin m → ℝ) =>
          ω (targetCoordinateFamily m i)) :=
        (measurable_pi_apply (targetCoordinateFamily m i)).comp (comap_measurable _)
      exact hω.aestronglyMeasurable
    · filter_upwards [] with ω
      exact PiLp.norm_apply_le
        (WithLp.toLp 2 (fun j => ω (targetCoordinateFamily m j))) i
  have hcoord_int : ∀ i : Fin m, Integrable
      (fun ω : WeakDual ℝ (Fin m → ℝ) => ω (targetCoordinateFamily m i)) P := by
    intro i
    exact (hcoord_mem i).integrable (by norm_num)
  have hsum_int : Integrable
      (fun ω : WeakDual ℝ (Fin m → ℝ) =>
        ∑ i : Fin m, t i * ω (targetCoordinateFamily m i)) P := by
    apply integrable_finset_sum
    intro i hi
    exact (hcoord_int i).const_mul (t i)
  have hzero : ∫ ω : WeakDual ℝ (Fin m → ℝ),
      (∑ i : Fin m, t i * ω (targetCoordinateFamily m i)) ∂P = 0 := by
    rw [integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro i hi
      rw [integral_const_mul]
      change t i * (∫ ω : WeakDual ℝ (Fin m → ℝ),
        ω (targetCoordinateFamily m i) ∂finiteCovarianceGaussianMeasure T) = 0
      rw [finiteCovarianceGaussianMeasure_eval_mean_zero]
      simp
    · intro i hi
      exact (hcoord_int i).const_mul (t i)
  rw [show (fun ω : WeakDual ℝ (Fin m → ℝ) =>
      inner ℝ t (WithLp.toLp 2 (fun i => ω (targetCoordinateFamily m i)))) =
      fun ω => ∑ i : Fin m, t i * ω (targetCoordinateFamily m i) by
    funext ω
    simp [PiLp.inner_apply, mul_comm]
  ]
  dsimp [P] at hzero
  exact hzero

theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_factor_centered
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ → BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g)))
    (hC : ∀ i j, C (fs i) (fs j) = periodicResolventCovarianceMatrix d m L mass hmass fs i j)
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hfactor : ∀ i j, @inner ℝ (EuclideanSpace ℝ (Fin m)) _
      (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) =
        periodicResolventCovarianceMatrix d m L mass hmass fs i j)
    (hquad₀ : ∀ t : EuclideanSpace ℝ (Fin m), Var[fun x => inner ℝ t x; targetCoordinateMeasure T] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j * C (fs i) (fs j)) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop (nhds (targetCoordinateProbabilityMeasure T)) := by
  exact physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_factor
    d m L mass hL hmass fs C hinner hC T hfactor
    (fun t => targetCoordinateMeasure_mean_zero T t) hquad₀

theorem targetCoordinateMeasure_projectedVariance_eq_covariance_quadratic {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (t : EuclideanSpace ℝ (Fin m)) :
    Var[fun z => inner ℝ t z; targetCoordinateMeasure T] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        @inner ℝ (EuclideanSpace ℝ (Fin m)) _
          (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) := by
  let μ : Measure (EuclideanSpace ℝ (Fin m)) := targetCoordinateMeasure T
  have hvec_mem : MemLp (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) 2 μ :=
    (targetCoordinateMeasure_hasGaussianLaw T).memLp_two
  have hcoord_mem : ∀ i : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => z i) 2 μ := by
    intro i
    apply (hvec_mem.norm).mono'
    · have hz : Measurable (fun z : EuclideanSpace ℝ (Fin m) => z i) :=
        (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin m → ℝ))
      exact hz.aestronglyMeasurable
    · filter_upwards [] with z
      exact PiLp.norm_apply_le z i
  have hprod_int : ∀ i j : Fin m,
      Integrable (fun z : EuclideanSpace ℝ (Fin m) => z i * z j) μ := by
    intro i j
    exact (hcoord_mem i).integrable_mul (hcoord_mem j)
  have hmeas : Measurable (fun z : EuclideanSpace ℝ (Fin m) => inner ℝ t z) := by
    fun_prop
  rw [variance_eq_integral hmeas.aemeasurable]
  rw [targetCoordinateMeasure_mean_zero T t]
  simp only [sub_zero]
  calc
    (∫ z : EuclideanSpace ℝ (Fin m), (inner ℝ t z) ^ 2 ∂μ) =
        ∫ z : EuclideanSpace ℝ (Fin m),
          (∑ i : Fin m, t i * z i) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp [PiLp.inner_apply, mul_comm]
    _ = ∫ z : EuclideanSpace ℝ (Fin m),
          ∑ i : Fin m, ∑ j : Fin m, (t i * t j) * (z i * z j) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [pow_two]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i : Fin m, ∑ j : Fin m, (t i * t j) *
          (∫ z : EuclideanSpace ℝ (Fin m), z i * z j ∂μ) := by
      rw [integral_finset_sum]
      · rw [Finset.sum_congr rfl]
        intro i hi
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro j hj
          rw [← integral_const_mul]
        · intro j hj
          exact (hprod_int i j).const_mul (t i * t j)
      · intro i hi
        apply integrable_finset_sum
        intro j hj
        exact (hprod_int i j).const_mul (t i * t j)
    _ = ∑ i : Fin m, ∑ j : Fin m, t i * t j *
          @inner ℝ (EuclideanSpace ℝ (Fin m)) _
            (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [targetCoordinateMeasure_covariance_entry T i j]

theorem targetCoordinateMeasure_covariance_quadratic_nonneg {m : ℕ}
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (t : EuclideanSpace ℝ (Fin m)) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, t i * t j *
      (∫ z : EuclideanSpace ℝ (Fin m), z i * z j ∂targetCoordinateMeasure T) := by
  calc
    0 ≤ Var[fun z => inner ℝ t z; targetCoordinateMeasure T] :=
      variance_nonneg _ _
    _ = ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        @inner ℝ (EuclideanSpace ℝ (Fin m)) _
          (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) :=
      targetCoordinateMeasure_projectedVariance_eq_covariance_quadratic T t
    _ = ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        (∫ z : EuclideanSpace ℝ (Fin m), z i * z j ∂targetCoordinateMeasure T) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [targetCoordinateMeasure_covariance_entry T i j]

theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_factor_concrete
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ → BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g)))
    (hC : ∀ i j, C (fs i) (fs j) = periodicResolventCovarianceMatrix d m L mass hmass fs i j)
    (T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hfactor : ∀ i j, @inner ℝ (EuclideanSpace ℝ (Fin m)) _
      (T (targetCoordinateFamily m i)) (T (targetCoordinateFamily m j)) =
        periodicResolventCovarianceMatrix d m L mass hmass fs i j) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop (nhds (targetCoordinateProbabilityMeasure T)) := by
  apply physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_factor_centered
    d m L mass hL hmass fs C hinner hC T hfactor
  intro t
  rw [targetCoordinateMeasure_projectedVariance_eq_covariance_quadratic T t]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hfactor i j, ← hC i j]

/-- The canonical Fourier target measure associated with the periodic resolvent covariance. -/
def periodicResolventTargetMeasure
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  targetCoordinateMeasure (periodicResolventCovarianceCanonicalFactor d m L mass hmass fs)

/-- Probability wrapper for the canonical Fourier target measure. -/
def periodicResolventTargetProbabilityMeasure
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) :=
  targetCoordinateProbabilityMeasure (periodicResolventCovarianceCanonicalFactor d m L mass hmass fs)

 theorem periodicResolventTargetMeasure_hasGaussianLaw
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    HasGaussianLaw id (periodicResolventTargetMeasure d m L mass hmass fs) := by
  exact targetCoordinateMeasure_hasGaussianLaw
    (periodicResolventCovarianceCanonicalFactor d m L mass hmass fs)

 theorem periodicResolventTargetMeasure_mean_zero
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    ∫ z, inner ℝ t z ∂periodicResolventTargetMeasure d m L mass hmass fs = 0 := by
  exact targetCoordinateMeasure_mean_zero
    (periodicResolventCovarianceCanonicalFactor d m L mass hmass fs) t

 theorem periodicResolventTargetMeasure_covariance_quadratic
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Var[fun z => inner ℝ t z; periodicResolventTargetMeasure d m L mass hmass fs] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        periodicResolventCovarianceMatrix d m L mass hmass fs i j := by
  change Var[fun z => inner ℝ t z;
      targetCoordinateMeasure (periodicResolventCovarianceCanonicalFactor d m L mass hmass fs)] = _
  rw [targetCoordinateMeasure_projectedVariance_eq_covariance_quadratic
    (periodicResolventCovarianceCanonicalFactor d m L mass hmass fs) t]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [periodicResolventCovarianceCanonicalFactor_gram
    d m L mass hL hmass fs i j]

/-- Canonical finite-dimensional convergence to the Fourier target probability measure. -/
theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_fourier_canonical
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ → BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g)))
    (hC : ∀ i j, C (fs i) (fs j) = periodicResolventCovarianceMatrix d m L mass hmass fs i j) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop
        (nhds (periodicResolventTargetProbabilityMeasure d m L mass hmass fs)) := by
  let T := periodicResolventCovarianceCanonicalFactor d m L mass hmass fs
  change Filter.Tendsto
    (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
      physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
    Filter.atTop (nhds (targetCoordinateProbabilityMeasure T))
  apply physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_factor_concrete
    d m L mass hL hmass fs C hinner hC T
  intro i j
  exact periodicResolventCovarianceCanonicalFactor_gram d m L mass hL hmass fs i j
/-- Unconditional periodic-resolvent finite-dimensional weak convergence, with the
Fourier-constructed target factor supplied internally. -/
theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_fourier
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ → BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g)))
    (hC : ∀ i j, C (fs i) (fs j) = periodicResolventCovarianceMatrix d m L mass hmass fs i j) :
    ∃ T : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m),
      Filter.Tendsto
        (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
          physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
        Filter.atTop (nhds (targetCoordinateProbabilityMeasure T)) := by
  obtain ⟨T, hT⟩ := finiteRealMatrix_factorization_of_posSemidef m
    (periodicResolventCovarianceMatrix d m L mass hmass fs)
    (periodicResolventCovarianceMatrix_matrix_posSemidef_of_fourier
      d m L mass hL hmass fs)
  refine ⟨T, ?_⟩
  exact physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_factor_concrete
    d m L mass hL hmass fs C hinner hC T hT

end Pphi2Clean.Continuum
