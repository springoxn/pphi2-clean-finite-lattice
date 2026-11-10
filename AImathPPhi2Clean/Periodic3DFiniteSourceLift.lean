import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
import AImathPPhi2Clean.Periodic3DSobolevWeights
import AImathPPhi2Clean.Periodic3DWeightedCarrier
import AImathPPhi2Clean.PhysicalLatticeSampling
import AImathPPhi2Clean.LatticeGaussianContinuumConsumer
import AImathPPhi2Clean.RealFourierTestFunctions

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Pphi2Clean.UpstreamLattice

def periodic3DComplexFourierLift (L : ℝ) (hL : 0 < L)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 3 → ℝ) ℝ)) :
    Periodic3DIndex → ℂ :=
  fun k => (ω (periodicCosineTest 3 L k hL) : ℂ) +
    (ω (periodicSineTest 3 L k hL) : ℂ) * Complex.I

theorem measurable_periodic3DComplexFourierLift (L : ℝ) (hL : 0 < L) :
    Measurable (periodic3DComplexFourierLift L hL) := by
  rw [measurable_pi_iff]
  intro k
  dsimp [periodic3DComplexFourierLift]
  have hcos : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin 3 → ℝ) ℝ) =>
        (ω (periodicCosineTest 3 L k hL) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply (periodicCosineTest 3 L k hL)).comp
        (comap_measurable _))
  have hsin : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin 3 → ℝ) ℝ) =>
        (ω (periodicSineTest 3 L k hL) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply (periodicSineTest 3 L k hL)).comp
        (comap_measurable _))
  exact hcos.add (hsin.mul_const Complex.I)

def periodic3DRawAtomicLift (N : ℕ) [NeZero N] (a L : ℝ) (hL : 0 < L) :
    FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) →
      Periodic3DIndex → ℂ :=
  fun ω => periodic3DComplexFourierLift L hL
    (latticeEmbedLift (physicalTestEval 3 N a) ω)

theorem measurable_periodic3DRawAtomicLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hL : 0 < L) : Measurable (periodic3DRawAtomicLift N a L hL) := by
  exact (measurable_periodic3DComplexFourierLift L hL).comp
    (latticeEmbedLift_measurable (physicalTestEval 3 N a))

theorem periodic3DComplexFourierLift_zero_mode (L : ℝ) (hL : 0 < L)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 3 → ℝ) ℝ)) :
    periodic3DComplexFourierLift L hL ω 0 = (ω 1 : ℂ) := by
  have hcos : periodicCosineTest 3 L 0 hL = (1 : BoundedContinuousFunction (Fin 3 → ℝ) ℝ) := by
    ext x
    simp [periodicCosineTest]
  have hsin : periodicSineTest 3 L 0 hL = (0 : BoundedContinuousFunction (Fin 3 → ℝ) ℝ) := by
    ext x
    simp [periodicSineTest]
  simp [periodic3DComplexFourierLift, hcos, hsin]

def periodic3DSitePhase (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) (k : Periodic3DIndex) : ℝ :=
  (2 * Real.pi / L) * ∑ i, (k i : ℝ) *
    latticePhysicalPoint 3 N a ((Fintype.equivFin (FinLatticeSites 3 N)).symm j) i

def periodic3DSiteSequence (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) : Periodic3DIndex → ℂ :=
  fun k => ((a ^ 3 * Real.cos (periodic3DSitePhase N a L j k) : ℝ) : ℂ) +
    ((a ^ 3 * Real.sin (periodic3DSitePhase N a L j k) : ℝ) : ℂ) * Complex.I

theorem periodic3DSiteSequence_mem_carrier (N : ℕ) [NeZero N]
    (a L : ℝ) (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DSiteSequence N a L j ∈ periodic3DCarrier 4 := by
  rw [periodic3DCarrier]
  have hmajor : Summable (fun k : Periodic3DIndex =>
      a ^ 6 * periodic3DHminusFourWeight k) :=
    periodic3DHminusFourWeight_summable.mul_left (a ^ 6)
  apply hmajor.of_nonneg_of_le
  · intro k
    exact mul_nonneg (periodic3DHminusFourWeight_nonneg k) (sq_nonneg _)
  · intro k
    let θ := periodic3DSitePhase N a L j k
    have hnorm : ‖periodic3DSiteSequence N a L j k‖ ^ 2 = a ^ 6 := by
      dsimp [periodic3DSiteSequence, θ]
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      calc
        (a ^ 3 * Real.cos (periodic3DSitePhase N a L j k)) ^ 2 +
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) ^ 2 =
            a ^ 6 * (Real.cos (periodic3DSitePhase N a L j k) ^ 2 +
              Real.sin (periodic3DSitePhase N a L j k) ^ 2) := by ring
        _ = a ^ 6 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    rw [hnorm]
    exact (mul_comm _ _).le

theorem periodic3DRawAtomicLift_zero_mode (N : ℕ) [NeZero N]
    (a L : ℝ) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DRawAtomicLift N a L hL ω 0 =
      a ^ 3 * ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) := by
  rw [periodic3DRawAtomicLift, periodic3DComplexFourierLift_zero_mode]
  rw [latticeEmbedLift_eval]
  simp [physicalTestEval]
  push_cast
  rw [← Finset.sum_mul]
  exact mul_comm _ _

theorem periodic3DRawAtomicLift_mem_carrier (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DRawAtomicLift N a L hL ω ∈ periodic3DCarrier 4 := by
  have hcos (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω)
          (periodicCosineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.cos (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicCosineTest_apply 3 N a L ha k hL j]
    rfl
  have hsin (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω)
          (periodicSineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 3 N a L ha k hL j]
    rfl
  have hseq : periodic3DRawAtomicLift N a L hL ω =
      fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
          periodic3DSiteSequence N a L j k := by
    funext k
    simp only [periodic3DRawAtomicLift, periodic3DComplexFourierLift]
    rw [hcos k, hsin k]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
      Complex.ofReal_sin, periodic3DSiteSequence]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hseq, periodic3DCarrier]
  let s : Finset (Fin (Fintype.card (FinLatticeSites 3 N))) := Finset.univ
  let c : Fin (Fintype.card (FinLatticeSites 3 N)) → ℝ := fun j =>
    ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N)))
  let v : Fin (Fintype.card (FinLatticeSites 3 N)) → Periodic3DIndex → ℂ :=
    fun j => periodic3DSiteSequence N a L j
  let m : ℕ := s.card
  change Summable (fun k : Periodic3DIndex => periodic3DHminusFourWeight k *
    ‖∑ j ∈ s, (c j : ℂ) * v j k‖ ^ 2)
  have hsum : Summable (fun k : Periodic3DIndex =>
      ∑ j ∈ s, ‖c j‖ ^ 2 *
        (periodic3DHminusFourWeight k * ‖v j k‖ ^ 2)) := by
    apply summable_sum
    intro j hj
    exact Summable.mul_left (‖c j‖ ^ 2)
      (periodic3DSiteSequence_mem_carrier N a L j)
  have hmaj : Summable (fun k : Periodic3DIndex =>
      (m : ℝ) * ∑ j ∈ s, ‖c j‖ ^ 2 *
        (periodic3DHminusFourWeight k * ‖v j k‖ ^ 2)) :=
    Summable.mul_left (m : ℝ) hsum
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (periodic3DHminusFourWeight_nonneg k) (sq_nonneg _)
  · intro k
    calc
      periodic3DHminusFourWeight k * ‖∑ j ∈ s, (c j : ℂ) * v j k‖ ^ 2 ≤
          periodic3DHminusFourWeight k * (∑ j ∈ s, ‖(c j : ℂ) * v j k‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
            (fun j hj => norm_nonneg _))).2 (norm_sum_le s (fun j => (c j : ℂ) * v j k))
        · exact periodic3DHminusFourWeight_nonneg k
      _ ≤ periodic3DHminusFourWeight k *
          ((m : ℝ) * ∑ j ∈ s, ‖(c j : ℂ) * v j k‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq
          (periodic3DHminusFourWeight_nonneg k)
      _ = (m : ℝ) * ∑ j ∈ s, ‖c j‖ ^ 2 *
          (periodic3DHminusFourWeight k * ‖v j k‖ ^ 2) := by
        simp [m, mul_pow, Finset.mul_sum, sq_abs]
        ring_nf
  exact hmaj

end Pphi2Clean.Continuum
