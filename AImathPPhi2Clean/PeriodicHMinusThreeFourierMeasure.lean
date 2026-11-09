import AImathPPhi2Clean.PeriodicHMinusThreeCompletion
import AImathPPhi2Clean.PeriodicComplexFourierLift

noncomputable section

namespace Pphi2Clean.Continuum

open MeasureTheory
open Pphi2Clean.UpstreamLattice
open Classical

/-- The raw Fourier data, multiplied coordinatewise by the square-root H^-3
weight. This has not yet been shown to lie in the completed `lp` space. -/
def periodicHMinusThreeRawWeightedLift (L : ℝ) (hperiod : 0 < L)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) :
    PeriodicFourierIndex → ℂ :=
  periodicHMinusThreeWeightedCoefficients (periodicComplexFourierLift L hperiod ω)

theorem measurable_periodicHMinusThreeRawWeightedLift (L : ℝ) (hperiod : 0 < L) :
    Measurable (periodicHMinusThreeRawWeightedLift L hperiod) := by
  rw [measurable_pi_iff]
  intro k
  dsimp [periodicHMinusThreeRawWeightedLift,
    periodicHMinusThreeWeightedCoefficients, periodicComplexFourierLift,
    periodicComplexFourierProbe]
  have hcos : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
        (ω (periodicCosineTest 2 L k hperiod) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply (periodicCosineTest 2 L k hperiod)).comp
        (comap_measurable _))
  have hsin : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin 2 → ℝ) ℝ) =>
        (ω (periodicSineTest 2 L k hperiod) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply (periodicSineTest 2 L k hperiod)).comp
        (comap_measurable _))
  exact measurable_const.mul (hcos.add (hsin.mul_const Complex.I))

/-- Total H^-3 representative of the raw Fourier lift. On points where the
weighted sequence is not in `lp`, it is set to zero. This convention makes the
map total but does not assert that the exceptional set is null. -/
def periodicHMinusThreeTotalCarrierLift (L : ℝ) (hperiod : 0 < L)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) :
    PeriodicHMinusThreeCompletion := by
  let c := periodicHMinusThreeRawWeightedLift L hperiod ω
  exact if h : Memℓp c 2 then ⟨c, h⟩ else 0

/-- Fourier phase of a lattice site for the periodic cosine/sine probes. -/
def periodicHMinusThreeSitePhase (N : ℕ) [NeZero N] (a L : ℝ)
    (hperiod : 0 < L) (j : Fin (Fintype.card (FinLatticeSites 2 N)))
    (k : PeriodicFourierIndex) : ℝ :=
  (2 * Real.pi / L) * ∑ i,
    (k i : ℝ) * latticePhysicalPoint 2 N a
      ((Fintype.equivFin (FinLatticeSites 2 N)).symm j) i

def periodicHMinusTwoSiteSequence (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 2 N))) : (Fin 2 → ℤ) → ℂ :=
  fun k =>
    ((a ^ 2 * Real.cos (periodicHMinusThreeSitePhase N a L hperiod j k) : ℝ) : ℂ) +
      ((a ^ 2 * Real.sin (periodicHMinusThreeSitePhase N a L hperiod j k) : ℝ) : ℂ) * Complex.I

/-- In the actual two-dimensional Fourier index, a lattice site sequence is an
H^-2 coefficient sequence. The zero mode is retained through the full weight. -/
theorem periodicHMinusTwoSiteSequence_mem_carrier (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 2 N))) :
    periodicHMinusTwoSiteSequence N a L hperiod j ∈ periodicHMinusTwoCarrier := by
  rw [periodicHMinusTwoCarrier]
  have hmajor : Summable (fun k : PeriodicFourierIndex =>
      (a ^ 4) * periodicHMinusTwoFullWeight k) :=
    summable_periodicHMinusTwoFullWeight.mul_left (a ^ 4)
  have hsum : Summable (fun k : PeriodicFourierIndex =>
      periodicHMinusTwoFullWeight k *
        ‖periodicHMinusTwoSiteSequence N a L hperiod j k‖ ^ 2) := by
    apply hmajor.of_nonneg_of_le
    · intro k
      exact mul_nonneg (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _)
    · intro k
      let θ := periodicHMinusThreeSitePhase N a L hperiod j k
      have hz : ‖((a ^ 2 * Real.cos θ : ℝ) : ℂ) +
          ((a ^ 2 * Real.sin θ : ℝ) : ℂ) * Complex.I‖ ^ 2 =
          (a ^ 2 * Real.cos θ) ^ 2 + (a ^ 2 * Real.sin θ) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      have hnorm : ‖periodicHMinusTwoSiteSequence N a L hperiod j k‖ ^ 2 =
          a ^ 4 := by
        dsimp [periodicHMinusTwoSiteSequence]
        rw [hz]
        calc
          (a ^ 2 * Real.cos θ) ^ 2 + (a ^ 2 * Real.sin θ) ^ 2 =
              a ^ 4 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring_nf
          _ = a ^ 4 := by rw [Real.cos_sq_add_sin_sq, mul_one]
      rw [hnorm]
      simpa [mul_comm] using
        (le_refl (periodicHMinusTwoFullWeight k * a ^ 4))
  exact hsum

theorem periodicHMinusTwoDiscreteRawLift_mem_carrier
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N))) :
    periodicHMinusTwoDiscreteRawLift N a L hperiod ω ∈ periodicHMinusTwoCarrier := by
  have hcos (k : PeriodicFourierIndex) :
      (latticeEmbedLift (physicalTestEval 2 N a) ω)
          (periodicCosineTest 2 L k hperiod) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 2 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 2 N))) *
            (a ^ 2 * Real.cos (periodicHMinusThreeSitePhase N a L hperiod j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicCosineTest_apply 2 N a L ha k hperiod j]
    rfl
  have hsin (k : PeriodicFourierIndex) :
      (latticeEmbedLift (physicalTestEval 2 N a) ω)
          (periodicSineTest 2 L k hperiod) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 2 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 2 N))) *
            (a ^ 2 * Real.sin (periodicHMinusThreeSitePhase N a L hperiod j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 2 N a L ha k hperiod j]
    rfl
  have hseq : periodicHMinusTwoDiscreteRawLift N a L hperiod ω =
      fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 2 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 2 N))) : ℂ) *
          periodicHMinusTwoSiteSequence N a L hperiod j k := by
    funext k
    simp only [periodicHMinusTwoDiscreteRawLift, periodicHMinusTwoLiftMap,
      periodicComplexFourierLift, periodicComplexFourierProbe]
    rw [hcos k, hsin k]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
      Complex.ofReal_sin, periodicHMinusTwoSiteSequence]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hseq]
  let s : Finset (Fin (Fintype.card (FinLatticeSites 2 N))) := Finset.univ
  let c : Fin (Fintype.card (FinLatticeSites 2 N)) → ℝ := fun j =>
    ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 2 N)))
  let v : Fin (Fintype.card (FinLatticeSites 2 N)) →
      (Fin 2 → ℤ) → ℂ := fun j => periodicHMinusTwoSiteSequence N a L hperiod j
  let m : ℕ := s.card
  change Summable (fun k : Fin 2 → ℤ => periodicHMinusTwoFullWeight k *
    ‖∑ j ∈ s, (c j : ℂ) * v j k‖ ^ 2)
  have hmaj : Summable (fun k : Fin 2 → ℤ =>
      (m : ℝ) * (∑ j ∈ s, ‖c j‖ ^ 2 *
        (periodicHMinusTwoFullWeight k * ‖v j k‖ ^ 2))) := by
    have hsum : Summable (fun k : Fin 2 → ℤ =>
        ∑ j ∈ s, ‖c j‖ ^ 2 *
          (periodicHMinusTwoFullWeight k * ‖v j k‖ ^ 2)) := by
      apply summable_sum
      intro j hj
      exact Summable.mul_left (‖c j‖ ^ 2)
        (periodicHMinusTwoSiteSequence_mem_carrier N a L hperiod j)
    exact Summable.mul_left (m : ℝ) hsum
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (periodicHMinusTwoFullWeight_nonneg k) (sq_nonneg _))
  · intro k
    calc
      periodicHMinusTwoFullWeight k *
          ‖∑ j ∈ s, (c j : ℂ) * v j k‖ ^ 2 ≤
          periodicHMinusTwoFullWeight k *
            (∑ j ∈ s, ‖(c j : ℂ) * v j k‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
            (fun j hj => norm_nonneg _))).2
            (norm_sum_le s (fun j => (c j : ℂ) * v j k))
        · exact periodicHMinusTwoFullWeight_nonneg k
      _ ≤ periodicHMinusTwoFullWeight k *
          ((m : ℝ) * (∑ j ∈ s, ‖(c j : ℂ) * v j k‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq
          (periodicHMinusTwoFullWeight_nonneg k)
      _ = (m : ℝ) * (∑ j ∈ s, ‖c j‖ ^ 2 *
          (periodicHMinusTwoFullWeight k * ‖v j k‖ ^ 2)) := by
        simp [m, mul_pow, Finset.mul_sum, sq_abs]
        ring_nf
  exact hmaj

def periodicHMinusThreeSiteWeightedSequence (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 2 N))) : PeriodicFourierIndex → ℂ :=
  fun k => (Real.sqrt (periodicHMinusThreeWeight k) : ℂ) *
    (((a ^ 2 * Real.cos (periodicHMinusThreeSitePhase N a L hperiod j k) : ℝ) : ℂ) +
      ((a ^ 2 * Real.sin (periodicHMinusThreeSitePhase N a L hperiod j k) : ℝ) : ℂ) * Complex.I)

theorem periodicHMinusThreeSiteWeightedSequence_memLp (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 2 N))) :
    Memℓp (periodicHMinusThreeSiteWeightedSequence N a L hperiod j) 2 := by
  have hmajor : Summable (fun k : PeriodicFourierIndex =>
      (2 * a ^ 4) * periodicHMinusThreeWeight k) :=
    summable_periodicHMinusThreeWeight.mul_left (2 * a ^ 4)
  have hsum : Summable (fun k : PeriodicFourierIndex =>
      ‖periodicHMinusThreeSiteWeightedSequence N a L hperiod j k‖ ^ (2 : ℝ)) := by
    apply hmajor.of_nonneg_of_le
    · intro k
      positivity
    · intro k
      let θ := periodicHMinusThreeSitePhase N a L hperiod j k
      have hw := periodicHMinusThreeWeight_nonneg k
      have hroot : ‖(Real.sqrt (periodicHMinusThreeWeight k) : ℂ)‖ ^ 2 =
          periodicHMinusThreeWeight k := by
        simp [Complex.norm_def, Complex.normSq_ofReal, Real.sq_sqrt hw]
      have hz : ‖((a ^ 2 * Real.cos θ : ℝ) : ℂ) +
          ((a ^ 2 * Real.sin θ : ℝ) : ℂ) * Complex.I‖ ^ 2 =
          (a ^ 2 * Real.cos θ) ^ 2 + (a ^ 2 * Real.sin θ) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      have hnorm : ‖periodicHMinusThreeSiteWeightedSequence N a L hperiod j k‖ ^ 2 =
          periodicHMinusThreeWeight k * a ^ 4 := by
        dsimp [periodicHMinusThreeSiteWeightedSequence]
        rw [norm_mul, mul_pow, hroot, hz]
        calc
          periodicHMinusThreeWeight k *
              ((a ^ 2 * Real.cos θ) ^ 2 + (a ^ 2 * Real.sin θ) ^ 2) =
              periodicHMinusThreeWeight k *
                (a ^ 4 * (Real.cos θ ^ 2 + Real.sin θ ^ 2)) := by ring
          _ = periodicHMinusThreeWeight k * a ^ 4 := by
            rw [Real.cos_sq_add_sin_sq, mul_one]
      rw [Real.rpow_two, hnorm]
      have hprod : 0 ≤ a ^ 4 * periodicHMinusThreeWeight k := by positivity
      nlinarith [hprod]
  simpa using (memℓp_gen (p := (2 : ENNReal)) hsum)

def periodicHMinusThreeSiteVector (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 2 N))) : PeriodicHMinusThreeCompletion :=
  ⟨periodicHMinusThreeSiteWeightedSequence N a L hperiod j,
    periodicHMinusThreeSiteWeightedSequence_memLp N a L hperiod j⟩

def periodicHMinusThreeFiniteSourceCoefficientMap (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (c : Fin (Fintype.card (FinLatticeSites 2 N)) → ℝ) :
    PeriodicHMinusThreeCompletion :=
  ∑ j : Fin (Fintype.card (FinLatticeSites 2 N)),
    c j • periodicHMinusThreeSiteVector N a L hperiod j

theorem continuous_periodicHMinusThreeFiniteSourceCoefficientMap (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L) :
    Continuous (periodicHMinusThreeFiniteSourceCoefficientMap N a L hperiod) := by
  unfold periodicHMinusThreeFiniteSourceCoefficientMap
  exact continuous_finsetSum Finset.univ (fun j _ =>
    (continuous_apply j).smul continuous_const)

def periodicHMinusThreeFiniteSourceFourierLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N))) :
    PeriodicHMinusThreeCompletion :=
  periodicHMinusThreeFiniteSourceCoefficientMap N a L hperiod
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 2 N))))

theorem measurable_periodicHMinusThreeFiniteSourceFourierLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L) :
    Measurable (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod) := by
  unfold periodicHMinusThreeFiniteSourceFourierLift
  have hcoords : Measurable (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 2 N)) =>
        fun j : Fin (Fintype.card (FinLatticeSites 2 N)) =>
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 2 N)))) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 2 N)))).comp (comap_measurable _)
  exact (continuous_periodicHMinusThreeFiniteSourceCoefficientMap N a L hperiod).measurable.comp hcoords

theorem periodicHMinusThreeFiniteSourceFourierLift_apply
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)))
    (k : PeriodicFourierIndex) :
    periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω k =
      ∑ j : Fin (Fintype.card (FinLatticeSites 2 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 2 N))) : ℂ) *
          periodicHMinusThreeSiteWeightedSequence N a L hperiod j k := by
  change (⇑(periodicHMinusThreeFiniteSourceCoefficientMap N a L hperiod
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 2 N)))))) k = _
  rw [periodicHMinusThreeFiniteSourceCoefficientMap, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    periodicHMinusThreeSiteVector, Complex.real_smul]

theorem periodicHMinusThreeRawWeightedLift_eq_finiteSourceFourierLift
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N))) :
    periodicHMinusThreeRawWeightedLift L hperiod
      (latticeEmbedLift (physicalTestEval 2 N a) ω) =
      fun k => periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω k := by
  have hcos (k : PeriodicFourierIndex) :
      (latticeEmbedLift (physicalTestEval 2 N a) ω)
          (periodicCosineTest 2 L k hperiod) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 2 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 2 N))) *
            (a ^ 2 * Real.cos (periodicHMinusThreeSitePhase N a L hperiod j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicCosineTest_apply 2 N a L ha k hperiod j]
    rfl
  have hsin (k : PeriodicFourierIndex) :
      (latticeEmbedLift (physicalTestEval 2 N a) ω)
          (periodicSineTest 2 L k hperiod) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 2 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 2 N))) *
            (a ^ 2 * Real.sin (periodicHMinusThreeSitePhase N a L hperiod j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 2 N a L ha k hperiod j]
    rfl
  funext k
  simp only [periodicHMinusThreeRawWeightedLift,
    periodicHMinusThreeWeightedCoefficients, periodicComplexFourierLift,
    periodicComplexFourierProbe]
  rw [hcos k, hsin k, periodicHMinusThreeFiniteSourceFourierLift_apply]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
    Complex.ofReal_sin, periodicHMinusThreeSiteWeightedSequence,
    periodicHMinusThreeSitePhase]
  rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem periodicHMinusThreeFiniteSourceFourierLift_eq_totalCarrierLift
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N))) :
    periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω =
      periodicHMinusThreeTotalCarrierLift L hperiod
        (latticeEmbedLift (physicalTestEval 2 N a) ω) := by
  have hseq := periodicHMinusThreeRawWeightedLift_eq_finiteSourceFourierLift
    N a L ha hperiod ω
  have hmem : Memℓp (periodicHMinusThreeRawWeightedLift L hperiod
      (latticeEmbedLift (physicalTestEval 2 N a) ω)) 2 := by
    rw [hseq]
    exact lp.memℓp (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω)
  apply Subtype.ext
  simp only [periodicHMinusThreeTotalCarrierLift, dif_pos hmem]
  exact hseq.symm

theorem periodicHMinusThreeFiniteSourceFourierLift_cylinder_apply
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)))
    (m : ℕ) (modes : Fin m → PeriodicFourierIndex) (i : Fin m) :
    periodicHMinusThreeCylinderMap m modes
      (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω) i =
      ∑ j : Fin (Fintype.card (FinLatticeSites 2 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 2 N))) : ℂ) *
          periodicHMinusThreeSiteWeightedSequence N a L hperiod j (modes i) := by
  rw [periodicHMinusThreeCylinderMap_apply]
  exact periodicHMinusThreeFiniteSourceFourierLift_apply
    N a L hperiod ω (modes i)

theorem periodicHMinusThreeDiscreteCarrierLift_cylinder_eq_finiteSource
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 2 N)))
    (m : ℕ) (modes : Fin m → PeriodicFourierIndex) :
    periodicHMinusThreeCylinderMap m modes
        (periodicHMinusThreeTotalCarrierLift L hperiod
          (latticeEmbedLift (physicalTestEval 2 N a) ω)) =
      periodicHMinusThreeCylinderMap m modes
        (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω) := by
  rw [periodicHMinusThreeFiniteSourceFourierLift_eq_totalCarrierLift
    N a L ha hperiod ω]

theorem measurable_periodicHMinusThreeDiscreteCarrierLift
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L) :
    Measurable (periodicHMinusThreeTotalCarrierLift L hperiod ∘
      latticeEmbedLift (physicalTestEval 2 N a)) := by
  have hfun : periodicHMinusThreeTotalCarrierLift L hperiod ∘
      latticeEmbedLift (physicalTestEval 2 N a) =
      periodicHMinusThreeFiniteSourceFourierLift N a L hperiod := by
    funext ω
    exact (periodicHMinusThreeFiniteSourceFourierLift_eq_totalCarrierLift
      N a L ha hperiod ω).symm
  rw [hfun]
  exact measurable_periodicHMinusThreeFiniteSourceFourierLift N a L hperiod

def PeriodicHMinusThreeLiftMeasureInput
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L) : Prop :=
  AEMeasurable (periodicHMinusThreeTotalCarrierLift L hperiod)
      (physicalGJMeasure 2 N a mass ha hmass) ∧
    ∀ᵐ ω ∂physicalGJMeasure 2 N a mass ha hmass,
      ∀ k, periodicHMinusThreeTotalCarrierLift L hperiod ω k =
        periodicHMinusThreeRawWeightedLift L hperiod ω k

/-- The H^-3 law obtained by pushing the actual physical lattice measure through
the total carrier representative. -/
def periodicHMinusThreeLatticeMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L) :
    Measure PeriodicHMinusThreeCompletion :=
  Measure.map (periodicHMinusThreeTotalCarrierLift L hperiod)
    (physicalGJMeasure 2 N a mass ha hmass)


/-- The same law written directly as a pushforward of the finite Gaussian source.
The lift is composed with the existing physical lattice embedding. -/
def periodicHMinusThreeFiniteSourceMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L) :
    Measure PeriodicHMinusThreeCompletion :=
  Measure.map
    (periodicHMinusThreeTotalCarrierLift L hperiod ∘
      latticeEmbedLift (physicalTestEval 2 N a))
    (finiteCovarianceGaussianMeasure
      (numberedLatticeCovarianceGJ 2 N a mass ha hmass))

theorem periodicHMinusThreeFiniteSourceFourierLift_map_eq_finiteSourceMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L) :
    Measure.map (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass)) =
      periodicHMinusThreeFiniteSourceMeasure N a mass L ha hmass hperiod := by
  unfold periodicHMinusThreeFiniteSourceMeasure
  apply Measure.map_congr
  filter_upwards [] with ω
  exact (periodicHMinusThreeFiniteSourceFourierLift_eq_totalCarrierLift
    N a L ha hperiod ω)


/-- The physical-measure pushforward agrees with the finite-source map
whenever the total carrier lift is almost-everywhere measurable. -/
theorem periodicHMinusThreeLatticeMeasure_eq_finiteSourceMap
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (hF : AEMeasurable (periodicHMinusThreeTotalCarrierLift L hperiod)
      (physicalGJMeasure 2 N a mass ha hmass)) :
    periodicHMinusThreeLatticeMeasure N a mass L ha hmass hperiod =
      periodicHMinusThreeFiniteSourceMeasure N a mass L ha hmass hperiod := by
  unfold periodicHMinusThreeLatticeMeasure periodicHMinusThreeFiniteSourceMeasure
    physicalGJMeasure
  exact AEMeasurable.map_map_of_aemeasurable hF
    (latticeEmbedLift_measurable (physicalTestEval 2 N a)).aemeasurable

theorem periodicHMinusThreeFiniteSourceFourierLift_map_eq_latticeMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (hinput : PeriodicHMinusThreeLiftMeasureInput N a mass L ha hmass hperiod) :
    Measure.map (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass)) =
      periodicHMinusThreeLatticeMeasure N a mass L ha hmass hperiod := by
  rcases hinput with ⟨hmeas, _⟩
  have hbridge : ∀ᵐ ω ∂finiteCovarianceGaussianMeasure
      (numberedLatticeCovarianceGJ 2 N a mass ha hmass),
      periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω =
        periodicHMinusThreeTotalCarrierLift L hperiod
          (latticeEmbedLift (physicalTestEval 2 N a) ω) := by
    filter_upwards [] with ω
    exact periodicHMinusThreeFiniteSourceFourierLift_eq_totalCarrierLift
      N a L ha hperiod ω
  calc
    Measure.map (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod)
        (finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 2 N a mass ha hmass)) =
        periodicHMinusThreeFiniteSourceMeasure N a mass L ha hmass hperiod := by
      exact Measure.map_congr hbridge
    _ = periodicHMinusThreeLatticeMeasure N a mass L ha hmass hperiod := by
      exact (periodicHMinusThreeLatticeMeasure_eq_finiteSourceMap N a mass L
        ha hmass hperiod hmeas).symm


/-- The finite-source pushforward written as a Borel probability measure. -/
noncomputable def periodicHMinusThreeFiniteSourceProbabilityMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L) :
    ProbabilityMeasure PeriodicHMinusThreeCompletion :=
  ProbabilityMeasure.map
    (⟨finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 2 N a mass ha hmass), by infer_instance⟩ :
      ProbabilityMeasure (FiniteLatticeConfiguration
        (Fintype.card (FinLatticeSites 2 N))))
    (f := periodicHMinusThreeFiniteSourceFourierLift N a L hperiod)

