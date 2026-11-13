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

/-- Flat periodicity of the cosine Fourier test. -/
theorem periodicCosineTest_flat_for_family
    (d : ℕ) (L : ℝ) (hL : 0 < L) (k : Fin d → ℤ) :
    IsFlatTorusPeriodic d L (periodicCosineTest d L k hL) := by
  intro x i
  simp only [periodicCosineTest_apply]
  have hsum :
      (∑ j, (k j : ℝ) * (if j = i then x j + L else x j)) =
        (∑ j, (k j : ℝ) * x j) + (k i : ℝ) * L := by
    calc
      _ = ∑ j, ((k j : ℝ) * x j + if j = i then (k j : ℝ) * L else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j = i <;> simp [hji, mul_add]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hangle :
      (2 * Real.pi / L) * ∑ j, (k j : ℝ) * (if j = i then x j + L else x j) =
        (2 * Real.pi / L) * ∑ j, (k j : ℝ) * x j + (k i : ℝ) * (2 * Real.pi) := by
    rw [hsum]
    field_simp
  rw [hangle, Real.cos_add_int_mul_two_pi]

/-- Flat periodicity of the sine Fourier test. -/
theorem periodicSineTest_flat_for_family
    (d : ℕ) (L : ℝ) (hL : 0 < L) (k : Fin d → ℤ) :
    IsFlatTorusPeriodic d L (periodicSineTest d L k hL) := by
  intro x i
  simp only [periodicSineTest_apply]
  have hsum :
      (∑ j, (k j : ℝ) * (if j = i then x j + L else x j)) =
        (∑ j, (k j : ℝ) * x j) + (k i : ℝ) * L := by
    calc
      _ = ∑ j, ((k j : ℝ) * x j + if j = i then (k j : ℝ) * L else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j = i <;> simp [hji, mul_add]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hangle :
      (2 * Real.pi / L) * ∑ j, (k j : ℝ) * (if j = i then x j + L else x j) =
        (2 * Real.pi / L) * ∑ j, (k j : ℝ) * x j + (k i : ℝ) * (2 * Real.pi) := by
    rw [hsum]
    field_simp
  rw [hangle, Real.sin_add_int_mul_two_pi]

/-- A finite periodic real Fourier family is flat-torus periodic. -/
theorem periodicFourierTestFamily_isFlatTorusPeriodic
    (d m : ℕ) (L : ℝ) (hL : 0 < L)
    (modes : Fin m → (Fin d → ℤ)) (useSine : Fin m → Bool) (i : Fin m) :
    IsFlatTorusPeriodic d L (periodicFourierTestFamily d m L hL modes useSine i) := by
  unfold periodicFourierTestFamily
  split
  · exact periodicSineTest_flat_for_family d L hL (modes i)
  · exact periodicCosineTest_flat_for_family d L hL (modes i)

/-- Actual finite Fourier coordinate laws converge to their centered periodic
resolvent Gaussian law in every dimension. -/
theorem physicalPeriodicFourierFamilyProbabilityMeasure_fixedVolume_tendsto
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → (Fin d → ℤ)) (useSine : Fin m → Bool) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure d N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
          (periodicFourierTestFamily d m L hL modes useSine))
      Filter.atTop
      (nhds (periodicResolventTargetProbabilityMeasure d m L mass hmass
        (periodicFourierTestFamily d m L hL modes useSine))) := by
  let fs := periodicFourierTestFamily d m L hL modes useSine
  let C : BoundedContinuousFunction (Fin d → ℝ) ℝ →
      BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ :=
    fun f g => (physicalTorusResolventPairing d L mass hmass f g).re
  have hinner : ∀ i j : Fin m, Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) (fs i)))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval d N (L / (N : ℝ))) (fs j))))
      Filter.atTop (nhds (C (fs i) (fs j))) := by
    intro i j
    change Filter.Tendsto (fixedVolumeCovarianceInner d L mass hL hmass (fs i) (fs j))
      Filter.atTop (nhds (C (fs i) (fs j)))
    simpa [C] using fixedVolumeCovarianceInner_tendsto_periodicMassiveResolvent
      d L mass hL hmass (fs i) (fs j)
      (periodicFourierTestFamily_isFlatTorusPeriodic d m L hL modes useSine i)
      (periodicFourierTestFamily_isFlatTorusPeriodic d m L hL modes useSine j)
  have hC : ∀ i j, C (fs i) (fs j) =
      periodicResolventCovarianceMatrix d m L mass hmass fs i j := by
    intro i j
    rfl
  simpa [fs] using
    physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_any_finite_test_family_indexed
      d m L mass hL hmass fs C hinner hC
