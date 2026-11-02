import AImathPPhi2Clean.FiniteRealFamilyWeakLimitInterface
import AImathPPhi2Clean.RealFourierTestFunctions

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory
open Pphi2Clean.UpstreamLattice

/-- A finite family of periodic cosine/sine test coordinates. `useSine i`
chooses the sine coordinate at mode `modes i`; otherwise the cosine coordinate
is used. -/
def periodicFourierTestFamily (d m : ℕ) (L : ℝ) (hL : 0 < L)
    (modes : Fin m → (Fin d → ℤ)) (useSine : Fin m → Bool) :
    Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ :=
  fun i => if useSine i then
    periodicSineTest d L (modes i) hL
  else periodicCosineTest d L (modes i) hL

@[simp] theorem periodicFourierTestFamily_apply_of_sine
    (d m : ℕ) (L : ℝ) (hL : 0 < L)
    (modes : Fin m → (Fin d → ℤ)) (useSine : Fin m → Bool)
    (i : Fin m) (hi : useSine i = true) :
    periodicFourierTestFamily d m L hL modes useSine i =
      periodicSineTest d L (modes i) hL := by
  simp [periodicFourierTestFamily, hi]

@[simp] theorem periodicFourierTestFamily_apply_of_cosine
    (d m : ℕ) (L : ℝ) (hL : 0 < L)
    (modes : Fin m → (Fin d → ℤ)) (useSine : Fin m → Bool)
    (i : Fin m) (hi : useSine i = false) :
    periodicFourierTestFamily d m L hL modes useSine i =
      periodicCosineTest d L (modes i) hL := by
  simp [periodicFourierTestFamily, hi]

/-- Uniform finite-family convergence entry point. The family `fs` is arbitrary:
it may contain Fourier cosine/sine tests, mixed Fourier/test coordinates, or
repeated coordinates. The covariance limit is the canonical periodic resolvent
matrix for exactly that family. -/
theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_any_finite_test_family
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ →
      BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
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
    (hC : ∀ i j, C (fs i) (fs j) =
      periodicResolventCovarianceMatrix d m L mass hmass fs i j) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop
      (nhds (periodicResolventTargetProbabilityMeasure d m L mass hmass fs)) := by
  exact physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_fourier_canonical
    d m L mass hL hmass fs C hinner hC

/-- The target Gaussian has zero mean in every finite coordinate direction. -/
theorem periodicResolventTargetMeasure_any_finite_mean_zero
    (d m : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    ∫ z, inner ℝ t z ∂periodicResolventTargetMeasure d m L mass hmass fs = 0 :=
  periodicResolventTargetMeasure_mean_zero d m L mass hmass fs t

/-- The target Gaussian covariance for every finite family is the quadratic form
of the periodic resolvent covariance matrix. -/
theorem periodicResolventTargetMeasure_any_finite_covariance
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Var[fun z => inner ℝ t z;
      periodicResolventTargetMeasure d m L mass hmass fs] =
      ∑ i : Fin m, ∑ j : Fin m, t i * t j *
        periodicResolventCovarianceMatrix d m L mass hmass fs i j :=
  periodicResolventTargetMeasure_covariance_quadratic d m L mass hL hmass fs t

theorem physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_any_finite_test_family_indexed
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ →
      BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
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
    (hC : ∀ i j, C (fs i) (fs j) =
      periodicResolventCovarianceMatrix d m L mass hmass fs i j) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass fs)
      Filter.atTop
      (nhds (periodicResolventTargetProbabilityMeasure d m L mass hmass fs)) := by
  apply physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_target_indexed
    d m L mass hL hmass fs C hinner
    (periodicResolventTargetProbabilityMeasure d m L mass hmass fs)
    (periodicResolventTargetMeasure_hasGaussianLaw d m L mass hmass fs)
    (periodicResolventTargetMeasure_mean_zero d m L mass hmass fs)
  intro t
  change Var[fun x => inner ℝ t x;
      periodicResolventTargetMeasure d m L mass hmass fs] = _
  rw [periodicResolventTargetMeasure_any_finite_covariance d m L mass hL hmass fs t]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← hC i j]

