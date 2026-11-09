import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import AImathPPhi2Clean.GaussianConfiguration
import AImathPPhi2Clean.FiniteFourierCoordinateConvergence
import AImathPPhi2Clean.PeriodicHMinusThreeCylinderConvergence
import AImathPPhi2Clean.RealFourierSecondMoment
import AImathPPhi2Clean.PhysicalLatticeGaussianLaw
import AImathPPhi2Clean.PeriodicFS4DWeightedCarrier
import AImathPPhi2Clean.PeriodicFS4DRealCarrier
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

noncomputable section

namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.UpstreamLattice

/-- The 4D complex probe, before identifying it with a raw-lift Fourier coefficient. -/
def fs4PeriodicComplexFourierProbe (L : ℝ) (hperiod : 0 < L)
    (k : FS4Index)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 4 → ℝ) ℝ)) : ℂ :=
  (ω (periodicCosineTest 4 L k hperiod) : ℂ) +
    (ω (periodicSineTest 4 L k hperiod) : ℂ) * Complex.I

@[simp] theorem fs4PeriodicComplexFourierProbe_norm_sq (L : ℝ) (hperiod : 0 < L)
    (k : FS4Index)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 4 → ℝ) ℝ)) :
    ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2 =
      (ω (periodicCosineTest 4 L k hperiod)) ^ 2 +
        (ω (periodicSineTest 4 L k hperiod)) ^ 2 := by
  unfold fs4PeriodicComplexFourierProbe
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

def fs4PeriodicComplexFourierLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    FS4Index → ℂ :=
  fun k => fs4PeriodicComplexFourierProbe L hperiod k
    (latticeEmbedLift (physicalTestEval 4 N a) ω)

@[simp] theorem fs4PeriodicComplexFourierLift_apply (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (k : FS4Index) :
    fs4PeriodicComplexFourierLift N a L hperiod ω k =
      fs4PeriodicComplexFourierProbe L hperiod k
        (latticeEmbedLift (physicalTestEval 4 N a) ω) := rfl

def fs4PeriodicComplexFourierProbeMoment (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) (k : FS4Index) : ℝ :=
  ∫ ω, ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2 ∂
    physicalGJMeasure 4 N a mass ha hmass

theorem fs4PeriodicComplexFourierLift_measurable
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L) :
    Measurable (fs4PeriodicComplexFourierLift N a L hperiod) := by
  rw [measurable_pi_iff]
  intro k
  have hcos : Measurable (fun w : WeakDual ℝ
      (BoundedContinuousFunction (Fin 4 → ℝ) ℝ) =>
      (w (periodicCosineTest 4 L k hperiod) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply (periodicCosineTest 4 L k hperiod)).comp
        (comap_measurable _))
  have hsin : Measurable (fun w : WeakDual ℝ
      (BoundedContinuousFunction (Fin 4 → ℝ) ℝ) =>
      (w (periodicSineTest 4 L k hperiod) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply (periodicSineTest 4 L k hperiod)).comp
        (comap_measurable _))
  have hprobe : Measurable (fun w : WeakDual ℝ
      (BoundedContinuousFunction (Fin 4 → ℝ) ℝ) =>
      fs4PeriodicComplexFourierProbe L hperiod k w) := by
    change Measurable (fun w : WeakDual ℝ
      (BoundedContinuousFunction (Fin 4 → ℝ) ℝ) =>
      (w (periodicCosineTest 4 L k hperiod) : ℂ) +
        (w (periodicSineTest 4 L k hperiod) : ℂ) * Complex.I)
    exact hcos.add (hsin.mul_const Complex.I)
  exact hprobe.comp
    (latticeEmbedLift_measurable (physicalTestEval 4 N a))

theorem fs4PeriodicComplexFourierLift_integral_eq_probeMoment
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (k : FS4Index) :
    ∫ ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)),
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2 ∂
      finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 4 N a mass ha hmass) =
      fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
  let μ := physicalGJMeasure 4 N a mass ha hmass
  have hcos := physicalGJMeasure_eval_hasGaussianLaw 4 N a mass ha hmass
    (periodicCosineTest 4 L k hperiod)
  have hsin := physicalGJMeasure_eval_hasGaussianLaw 4 N a mass ha hmass
    (periodicSineTest 4 L k hperiod)
  have hcosI : Integrable (fun ω =>
      (ω (periodicCosineTest 4 L k hperiod)) ^ 2) μ :=
    hcos.memLp_two.integrable_sq
  have hsinI : Integrable (fun ω =>
      (ω (periodicSineTest 4 L k hperiod)) ^ 2) μ :=
    hsin.memLp_two.integrable_sq
  have hprobeI : Integrable (fun ω =>
      ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2) μ := by
    have hadd := hcosI.add hsinI
    apply hadd.congr
    filter_upwards [] with ω
    exact (fs4PeriodicComplexFourierProbe_norm_sq L hperiod k ω).symm
  have hmap := integral_map
    (latticeEmbedLift_measurable (physicalTestEval 4 N a)).aemeasurable
    hprobeI.aestronglyMeasurable
  have hmap' :
      (∫ ω, ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2 ∂μ) =
      (∫ ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)),
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2 ∂
          finiteCovarianceGaussianMeasure
            (numberedLatticeCovarianceGJ 4 N a mass ha hmass)) := by
    simpa [μ, physicalGJMeasure, fs4PeriodicComplexFourierLift,
      Function.comp_def] using hmap
  rw [← hmap']
  rfl

/-- Uniform 4D probe moment from the dimension-generic real-test estimate.
This is not yet a raw Fourier coefficient or an infinite trace theorem. -/
theorem fs4PeriodicComplexFourierProbeMoment_le (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) (k : FS4Index) :
    fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k ≤
      2 * (mass⁻¹ ^ 2 * L ^ 4) := by
  unfold fs4PeriodicComplexFourierProbeMoment
  have hcosLaw := physicalGJMeasure_eval_hasGaussianLaw 4 N a mass ha hmass
    (periodicCosineTest 4 L k hperiod)
  have hsinLaw := physicalGJMeasure_eval_hasGaussianLaw 4 N a mass ha hmass
    (periodicSineTest 4 L k hperiod)
  have hcosInt : Integrable (fun ω =>
      (ω (periodicCosineTest 4 L k hperiod)) ^ 2)
      (physicalGJMeasure 4 N a mass ha hmass) := hcosLaw.memLp_two.integrable_sq
  have hsinInt : Integrable (fun ω =>
      (ω (periodicSineTest 4 L k hperiod)) ^ 2)
      (physicalGJMeasure 4 N a mass ha hmass) := hsinLaw.memLp_two.integrable_sq
  have hcos := physicalGJMeasure_periodicCosineTest_second_moment_le
    4 N a mass L ha hmass hL k hperiod
  have hsin := physicalGJMeasure_periodicSineTest_second_moment_le
    4 N a mass L ha hmass hL k hperiod
  calc
    (∫ ω, ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2
        ∂physicalGJMeasure 4 N a mass ha hmass) =
      ∫ ω, (ω (periodicCosineTest 4 L k hperiod)) ^ 2 +
        (ω (periodicSineTest 4 L k hperiod)) ^ 2
        ∂physicalGJMeasure 4 N a mass ha hmass := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact fs4PeriodicComplexFourierProbe_norm_sq L hperiod k ω
    _ = (∫ ω, (ω (periodicCosineTest 4 L k hperiod)) ^ 2
          ∂physicalGJMeasure 4 N a mass ha hmass) +
        ∫ ω, (ω (periodicSineTest 4 L k hperiod)) ^ 2
          ∂physicalGJMeasure 4 N a mass ha hmass :=
          integral_add hcosInt hsinInt
    _ ≤ mass⁻¹ ^ 2 * L ^ 4 + mass⁻¹ ^ 2 * L ^ 4 := add_le_add hcos hsin
    _ = 2 * (mass⁻¹ ^ 2 * L ^ 4) := by ring

theorem fs4PeriodicComplexFourierProbe_weighted_trace_bound (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) :
    Summable (fun k : FS4Index => fs4SobolevWeight 3 k *
      fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) ∧
      ∑' k : FS4Index, fs4SobolevWeight 3 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k ≤
        (2 * (mass⁻¹ ^ 2 * L ^ 4)) * ∑' k : FS4Index, fs4SobolevWeight 3 k := by
  let C := 2 * (mass⁻¹ ^ 2 * L ^ 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hweight := fs4HMinusThreeWeight_summable
  have hmajor : Summable (fun k : FS4Index => C * fs4SobolevWeight 3 k) :=
    hweight.mul_left C
  have hnonneg : ∀ k : FS4Index, 0 ≤
      fs4SobolevWeight 3 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
    intro k
    apply mul_nonneg (fs4SobolevWeight_nonneg 3 k)
    unfold fs4PeriodicComplexFourierProbeMoment
    exact integral_nonneg (fun ω => sq_nonneg
      ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖)
  have hle : ∀ k : FS4Index,
      fs4SobolevWeight 3 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k ≤
      C * fs4SobolevWeight 3 k := by
    intro k
    calc
      fs4SobolevWeight 3 k *
          fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k ≤
        fs4SobolevWeight 3 k * C :=
          mul_le_mul_of_nonneg_left
            (fs4PeriodicComplexFourierProbeMoment_le N a mass L ha hmass hL hperiod k)
            (fs4SobolevWeight_nonneg 3 k)
      _ = C * fs4SobolevWeight 3 k := by ring
  have hsum : Summable (fun k : FS4Index =>
      fs4SobolevWeight 3 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) :=
    hmajor.of_nonneg_of_le hnonneg hle
  refine ⟨hsum, ?_⟩
  have htsum := hsum.tsum_le_tsum hle hmajor
  simpa [C, tsum_mul_left] using htsum

def fs4PeriodicFourierSitePhase (N : ℕ) [NeZero N] (a L : ℝ)
    (hperiod : 0 < L) (j : Fin (Fintype.card (FinLatticeSites 4 N)))
    (k : FS4Index) : ℝ :=
  (2 * Real.pi / L) * ∑ i,
    (k i : ℝ) * latticePhysicalPoint 4 N a
      ((Fintype.equivFin (FinLatticeSites 4 N)).symm j) i

def fs4PeriodicFourierSiteSequence (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 4 N))) : FS4Index → ℂ :=
  fun k => ((a ^ 4 * Real.cos
      (fs4PeriodicFourierSitePhase N a L hperiod j k) : ℝ) : ℂ) +
    ((a ^ 4 * Real.sin
      (fs4PeriodicFourierSitePhase N a L hperiod j k) : ℝ) : ℂ) * Complex.I

theorem fs4PeriodicFourierSiteSequence_mem_carrier (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 4 N))) :
    fs4PeriodicFourierSiteSequence N a L hperiod j ∈
      fs4HminusThreeCoefficientCarrier := by
  rw [fs4HminusThreeCoefficientCarrier]
  have hmajor : Summable (fun k : FS4Index =>
      (a ^ 8) * fs4SobolevWeight 3 k) :=
    fs4HMinusThreeWeight_summable.mul_left (a ^ 8)
  apply hmajor.of_nonneg_of_le
  · intro k
    exact mul_nonneg (fs4SobolevWeight_nonneg 3 k) (sq_nonneg _)
  · intro k
    let θ := fs4PeriodicFourierSitePhase N a L hperiod j k
    have hz : ‖((a ^ 4 * Real.cos θ : ℝ) : ℂ) +
        ((a ^ 4 * Real.sin θ : ℝ) : ℂ) * Complex.I‖ ^ 2 =
        (a ^ 4 * Real.cos θ) ^ 2 + (a ^ 4 * Real.sin θ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have hnorm :
        ‖fs4PeriodicFourierSiteSequence N a L hperiod j k‖ ^ 2 = a ^ 8 := by
      dsimp [fs4PeriodicFourierSiteSequence]
      rw [hz]
      calc
        (a ^ 4 * Real.cos θ) ^ 2 + (a ^ 4 * Real.sin θ) ^ 2 =
            a ^ 8 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring_nf
        _ = a ^ 8 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    rw [hnorm]
    exact le_of_eq (by ring : fs4SobolevWeight 3 k * a ^ 8 = a ^ 8 * fs4SobolevWeight 3 k)

theorem fs4PeriodicComplexFourierLift_mem_carrier
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    fs4PeriodicComplexFourierLift N a L hperiod ω ∈
      fs4HminusThreeCoefficientCarrier := by
  have hcos (k : FS4Index) :
      (latticeEmbedLift (physicalTestEval 4 N a) ω)
          (periodicCosineTest 4 L k hperiod) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 4 N))) *
            (a ^ 4 * Real.cos (fs4PeriodicFourierSitePhase N a L hperiod j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicCosineTest_apply 4 N a L ha k hperiod j]
    rfl
  have hsin (k : FS4Index) :
      (latticeEmbedLift (physicalTestEval 4 N a) ω)
          (periodicSineTest 4 L k hperiod) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 4 N))) *
            (a ^ 4 * Real.sin (fs4PeriodicFourierSitePhase N a L hperiod j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 4 N a L ha k hperiod j]
    rfl
  have hseq : fs4PeriodicComplexFourierLift N a L hperiod ω =
      fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 4 N))) : ℂ) *
          fs4PeriodicFourierSiteSequence N a L hperiod j k := by
    funext k
    simp only [fs4PeriodicComplexFourierLift, fs4PeriodicComplexFourierProbe]
    rw [hcos k, hsin k]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
      Complex.ofReal_sin, fs4PeriodicFourierSiteSequence]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hseq]
  let s : Finset (Fin (Fintype.card (FinLatticeSites 4 N))) := Finset.univ
  let c : Fin (Fintype.card (FinLatticeSites 4 N)) → ℝ := fun j =>
    ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 4 N)))
  let v : Fin (Fintype.card (FinLatticeSites 4 N)) → FS4Index → ℂ :=
    fun j => fs4PeriodicFourierSiteSequence N a L hperiod j
  let m : ℕ := s.card
  change Summable (fun k : FS4Index => fs4SobolevWeight 3 k *
    ‖∑ j ∈ s, (c j : ℂ) * v j k‖ ^ 2)
  have hmaj : Summable (fun k : FS4Index =>
      (m : ℝ) * (∑ j ∈ s, ‖c j‖ ^ 2 *
        (fs4SobolevWeight 3 k * ‖v j k‖ ^ 2))) := by
    have hsum : Summable (fun k : FS4Index =>
        ∑ j ∈ s, ‖c j‖ ^ 2 *
          (fs4SobolevWeight 3 k * ‖v j k‖ ^ 2)) := by
      apply summable_sum
      intro j hj
      exact Summable.mul_left (‖c j‖ ^ 2)
        (fs4PeriodicFourierSiteSequence_mem_carrier N a L hperiod j)
    exact Summable.mul_left (m : ℝ) hsum
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (fs4SobolevWeight_nonneg 3 k) (sq_nonneg _))
  · intro k
    calc
      fs4SobolevWeight 3 k *
          ‖∑ j ∈ s, (c j : ℂ) * v j k‖ ^ 2 ≤
        fs4SobolevWeight 3 k *
          (∑ j ∈ s, ‖(c j : ℂ) * v j k‖) ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
              (fun j hj => norm_nonneg _))).2
              (norm_sum_le s (fun j => (c j : ℂ) * v j k))
          · exact fs4SobolevWeight_nonneg 3 k
      _ ≤ fs4SobolevWeight 3 k *
          ((m : ℝ) * (∑ j ∈ s, ‖(c j : ℂ) * v j k‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq
            (fs4SobolevWeight_nonneg 3 k)
      _ = (m : ℝ) * (∑ j ∈ s, ‖c j‖ ^ 2 *
          (fs4SobolevWeight 3 k * ‖v j k‖ ^ 2)) := by
          simp [m, mul_pow, Finset.mul_sum, sq_abs]
          ring_nf
  · exact hmaj


instance instMeasurableSpaceFS4HminusThreeCompletion :
    MeasurableSpace FS4HminusThreeCompletion :=
  borel FS4HminusThreeCompletion

instance instBorelSpaceFS4HminusThreeCompletion :
    BorelSpace FS4HminusThreeCompletion := ⟨rfl⟩

def fs4PeriodicFourierSiteVector (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 4 N))) : FS4HminusThreeCompletion :=
  fs4HminusThreeEmbeddingOfCoefficients
    (fs4PeriodicFourierSiteSequence N a L hperiod j)
    (fs4PeriodicFourierSiteSequence_mem_carrier N a L hperiod j)

def fs4PeriodicFourierFiniteSourceCoefficientMap (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (c : Fin (Fintype.card (FinLatticeSites 4 N)) → ℝ) :
    FS4HminusThreeCompletion :=
  ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
    c j • fs4PeriodicFourierSiteVector N a L hperiod j

theorem continuous_fs4PeriodicFourierFiniteSourceCoefficientMap
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L) :
    Continuous (fs4PeriodicFourierFiniteSourceCoefficientMap N a L hperiod) := by
  unfold fs4PeriodicFourierFiniteSourceCoefficientMap
  exact continuous_finsetSum Finset.univ (fun j _ =>
    (continuous_apply j).smul continuous_const)

def fs4PeriodicFourierFiniteSourceCarrierLift (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    FS4HminusThreeCompletion :=
  fs4PeriodicFourierFiniteSourceCoefficientMap N a L hperiod
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 4 N))))

theorem measurable_fs4PeriodicFourierFiniteSourceCarrierLift
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L) :
    Measurable (fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod) := by
  unfold fs4PeriodicFourierFiniteSourceCarrierLift
  have hcoords : Measurable (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 4 N)) =>
        fun j : Fin (Fintype.card (FinLatticeSites 4 N)) =>
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 4 N)))) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 4 N)))).comp (comap_measurable _)
  exact (continuous_fs4PeriodicFourierFiniteSourceCoefficientMap N a L hperiod).measurable.comp hcoords

theorem fs4PeriodicFourierFiniteSourceCarrierLift_apply
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (k : FS4Index) :
    fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω k =
      ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 4 N))) : ℂ) *
          ((Real.sqrt (fs4SobolevWeight 3 k) : ℂ) *
            fs4PeriodicFourierSiteSequence N a L hperiod j k) := by
  change (⇑(fs4PeriodicFourierFiniteSourceCoefficientMap N a L hperiod
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 4 N))))) k) = _
  rw [fs4PeriodicFourierFiniteSourceCoefficientMap, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    fs4PeriodicFourierSiteVector, fs4HminusThreeEmbeddingOfCoefficients,
    fs4WeightedFourierCoefficients, Complex.real_smul]


theorem fs4PeriodicComplexFourierLift_eq_siteSum
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    fs4PeriodicComplexFourierLift N a L hperiod ω =
      fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 4 N))) : ℂ) *
          fs4PeriodicFourierSiteSequence N a L hperiod j k := by
  have hcos (k : FS4Index) :
      (latticeEmbedLift (physicalTestEval 4 N a) ω)
          (periodicCosineTest 4 L k hperiod) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 4 N))) *
            (a ^ 4 * Real.cos (fs4PeriodicFourierSitePhase N a L hperiod j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicCosineTest_apply 4 N a L ha k hperiod j]
    rfl
  have hsin (k : FS4Index) :
      (latticeEmbedLift (physicalTestEval 4 N a) ω)
          (periodicSineTest 4 L k hperiod) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 4 N))) *
            (a ^ 4 * Real.sin (fs4PeriodicFourierSitePhase N a L hperiod j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 4 N a L ha k hperiod j]
    rfl
  funext k
  simp only [fs4PeriodicComplexFourierLift, fs4PeriodicComplexFourierProbe]
  rw [hcos k, hsin k]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
    Complex.ofReal_sin, fs4PeriodicFourierSiteSequence]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem fs4PeriodicFourierFiniteSourceCarrierLift_eq_weightedRaw
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (k : FS4Index) :
    fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω k =
      (Real.sqrt (fs4SobolevWeight 3 k) : ℂ) *
        fs4PeriodicComplexFourierLift N a L hperiod ω k := by
  rw [fs4PeriodicFourierFiniteSourceCarrierLift_apply,
    fs4PeriodicComplexFourierLift_eq_siteSum N a L ha hperiod ω]
  calc
    _ = ∑ j, (Real.sqrt (fs4SobolevWeight 3 k) : ℂ) *
        ((ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 4 N))) : ℂ) *
          fs4PeriodicFourierSiteSequence N a L hperiod j k) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring


    _ = _ := by rw [Finset.mul_sum]
theorem fs4PeriodicComplexFourierLift_star_neg
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (k : FS4Index) :
    star (fs4PeriodicComplexFourierLift N a L hperiod ω (fun i => -k i)) =
      fs4PeriodicComplexFourierLift N a L hperiod ω k := by
  rw [fs4PeriodicComplexFourierLift_eq_siteSum N a L ha hperiod ω]
  simp only [fs4PeriodicFourierSiteSequence, fs4PeriodicFourierSitePhase]
  simp [← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
    Complex.conj_I, Real.cos_neg, Real.sin_neg, Finset.sum_neg_distrib,
    map_ofNat, map_mul, map_div₀]
theorem fs4PeriodicFourierFiniteSourceCarrierLift_mem_realCarrier
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω ∈
      fs4HminusFourRealCarrier := by
  intro k
  rw [fs4PeriodicFourierFiniteSourceCarrierLift_eq_weightedRaw
      N a L ha hperiod ω (fun i => -k i),
    fs4PeriodicFourierFiniteSourceCarrierLift_eq_weightedRaw
      N a L ha hperiod ω k]
  rw [fs4SobolevWeight_neg]
  have hstar := fs4PeriodicComplexFourierLift_star_neg N a L ha hperiod ω k
  rw [← hstar]
  simp
theorem fs4PeriodicFourierFiniteSourceCarrierLift_norm_sq
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ^ 2 =
      ∑' k : FS4Index, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal)
    (fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω)
  norm_num at hnorm
  rw [hnorm]
  apply tsum_congr
  intro k
  rw [fs4PeriodicFourierFiniteSourceCarrierLift_eq_weightedRaw
    N a L ha hperiod ω k]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt (fs4SobolevWeight_nonneg 3 k)]
theorem fs4PeriodicComplexFourierProbe_integral_tsum_eq_weighted_trace
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    ∑' k : FS4Index, ∫ ω, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2
      ∂physicalGJMeasure 4 N a mass ha hmass =
      ∫ ω, ∑' k : FS4Index, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2
      ∂physicalGJMeasure 4 N a mass ha hmass := by
  apply integral_tsum_of_summable_integral_norm
  · intro k
    have hcosLaw := physicalGJMeasure_eval_hasGaussianLaw 4 N a mass ha hmass
      (periodicCosineTest 4 L k hperiod)
    have hsinLaw := physicalGJMeasure_eval_hasGaussianLaw 4 N a mass ha hmass
      (periodicSineTest 4 L k hperiod)
    have hcosInt : Integrable (fun ω =>
        (ω (periodicCosineTest 4 L k hperiod)) ^ 2)
        (physicalGJMeasure 4 N a mass ha hmass) := hcosLaw.memLp_two.integrable_sq
    have hsinInt : Integrable (fun ω =>
        (ω (periodicSineTest 4 L k hperiod)) ^ 2)
        (physicalGJMeasure 4 N a mass ha hmass) := hsinLaw.memLp_two.integrable_sq
    have hadd := hcosInt.add hsinInt
    have hp : Integrable (fun ω => ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2)
        (physicalGJMeasure 4 N a mass ha hmass) := by
      apply hadd.congr
      filter_upwards [] with ω
      exact (fs4PeriodicComplexFourierProbe_norm_sq L hperiod k ω).symm
    exact hp.const_mul (fs4SobolevWeight 3 k)
  · have htrace := fs4PeriodicComplexFourierProbe_weighted_trace_bound
      N a mass L ha hmass hL hperiod
    have hsum : Summable (fun k : FS4Index =>
        fs4SobolevWeight 3 k *
          fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) := htrace.1
    apply hsum.congr
    intro k
    change fs4SobolevWeight 3 k *
        (∫ ω, ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖ ^ 2
          ∂physicalGJMeasure 4 N a mass ha hmass) = _
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (fs4SobolevWeight_nonneg 3 k) (sq_nonneg _))]
theorem fs4PeriodicFourierFiniteSourceCarrierLift_integral_tsum_eq_weighted_trace
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    ∑' k : FS4Index, ∫ ω, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 4 N a mass ha hmass) =
      ∫ ω, ∑' k : FS4Index, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 4 N a mass ha hmass) := by
  let T := numberedLatticeCovarianceGJ 4 N a mass ha hmass
  change (∑' k : FS4Index, ∫ ω, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2 ∂finiteCovarianceGaussianMeasure T) =
      ∫ ω, ∑' k : FS4Index, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2 ∂finiteCovarianceGaussianMeasure T
  apply integral_tsum_of_summable_integral_norm
  · intro k
    let fc := latticeTestField (physicalTestEval 4 N a)
      (periodicCosineTest 4 L k hperiod)
    let fs := latticeTestField (physicalTestEval 4 N a)
      (periodicSineTest 4 L k hperiod)
    have hcosLaw := finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T fc
    have hsinLaw := finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T fs
    have hcosInt : Integrable (fun ω => (ω fc) ^ 2)
        (finiteCovarianceGaussianMeasure T) := hcosLaw.memLp_two.integrable_sq
    have hsinInt : Integrable (fun ω => (ω fs) ^ 2)
        (finiteCovarianceGaussianMeasure T) := hsinLaw.memLp_two.integrable_sq
    have hadd := hcosInt.add hsinInt
    have hp : Integrable (fun ω => ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2)
        (finiteCovarianceGaussianMeasure T) := by
      apply hadd.congr
      filter_upwards [] with ω
      rw [fs4PeriodicComplexFourierLift_apply, fs4PeriodicComplexFourierProbe_norm_sq]
      rw [latticeEmbedLift_eval_eq, latticeEmbedLift_eval_eq]
      rfl
    exact hp.const_mul (fs4SobolevWeight 3 k)
  · have htrace := fs4PeriodicComplexFourierProbe_weighted_trace_bound
      N a mass L ha hmass hL hperiod
    have hsum : Summable (fun k : FS4Index =>
        fs4SobolevWeight 3 k *
          fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) := htrace.1
    apply hsum.congr
    intro k
    rw [← fs4PeriodicComplexFourierLift_integral_eq_probeMoment
      N a mass L ha hmass hperiod k]
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (fs4SobolevWeight_nonneg 3 k) (sq_nonneg _))]
theorem fs4PeriodicFourierFiniteSourceCarrierLift_integral_norm_sq_le
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    ∫ ω, ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ^ 2
      ∂finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 4 N a mass ha hmass) ≤
      (2 * (mass⁻¹ ^ 2 * L ^ 4)) * ∑' k : FS4Index,
        fs4SobolevWeight 3 k := by
  have hbridge := fs4PeriodicFourierFiniteSourceCarrierLift_integral_tsum_eq_weighted_trace
    N a mass L ha hmass hL hperiod
  have htrace := fs4PeriodicComplexFourierProbe_weighted_trace_bound
    N a mass L ha hmass hL hperiod
  calc
    ∫ ω, ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ^ 2
        ∂finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 4 N a mass ha hmass) =
      ∫ ω, ∑' k : FS4Index, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
        ∂finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 4 N a mass ha hmass) := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact (fs4PeriodicFourierFiniteSourceCarrierLift_norm_sq
              N a L ha hperiod ω)
    _ = ∑' k : FS4Index, ∫ ω, fs4SobolevWeight 3 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
        ∂finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 4 N a mass ha hmass) := hbridge.symm
    _ = ∑' k : FS4Index, fs4SobolevWeight 3 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
          apply tsum_congr
          intro k
          rw [integral_const_mul]
          congr 1
          exact fs4PeriodicComplexFourierLift_integral_eq_probeMoment
            N a mass L ha hmass hperiod k
    _ ≤ (2 * (mass⁻¹ ^ 2 * L ^ 4)) * ∑' k : FS4Index,
        fs4SobolevWeight 3 k := htrace.2
theorem fs4PeriodicFourierTestFamily_fixedVolume_weak_tendsto
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → (Fin 4 → ℤ)) (useSine : Fin m → Bool) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure 4 N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
          (periodicFourierTestFamily 4 m L hL modes useSine))
      Filter.atTop
      (nhds (periodicResolventTargetProbabilityMeasure 4 m L mass hmass
        (periodicFourierTestFamily 4 m L hL modes useSine))) := by
  let fs := periodicFourierTestFamily 4 m L hL modes useSine
  let C : BoundedContinuousFunction (Fin 4 → ℝ) ℝ →
      BoundedContinuousFunction (Fin 4 → ℝ) ℝ → ℝ := fun f g =>
        (torusFourierGreenPairing 4 L mass f g).re
  apply physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_any_finite_test_family_indexed
    4 m L mass hL hmass fs C
  · intro i j
    have hfi : IsFlatTorusPeriodic 4 L (fs i) := by
      dsimp [fs, periodicFourierTestFamily]
      split <;> rename_i h
      · exact periodicSineTest_isFlatTorusPeriodic 4 L hL (modes i)
      · exact periodicCosineTest_isFlatTorusPeriodic 4 L hL (modes i)
    have hfj : IsFlatTorusPeriodic 4 L (fs j) := by
      dsimp [fs, periodicFourierTestFamily]
      split <;> rename_i h
      · exact periodicSineTest_isFlatTorusPeriodic 4 L hL (modes j)
      · exact periodicCosineTest_isFlatTorusPeriodic 4 L hL (modes j)
    change Filter.Tendsto
      (fixedVolumeCovarianceInner 4 L mass hL hmass (fs i) (fs j))
      Filter.atTop (nhds (torusFourierGreenPairing 4 L mass (fs i) (fs j)).re)
    exact fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
      4 L mass hL hmass (fs i) (fs j) hfi hfj
  · intro i j
    unfold periodicResolventCovarianceMatrix
    rw [← torusFourierGreenPairing_eq_physicalTorusResolventPairing
      4 L mass hL hmass (fs i) (fs j)]
def fs4PeriodicFourierSiteVectorH4 (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L)
    (j : Fin (Fintype.card (FinLatticeSites 4 N))) : FS4HminusFourCompletion :=
  fs4HminusFourEmbeddingOfCoefficients
    (fs4PeriodicFourierSiteSequence N a L hperiod j)
    (fs4_hminus3_coefficients_in_hminus4
      (fs4PeriodicFourierSiteSequence N a L hperiod j)
      (fs4PeriodicFourierSiteSequence_mem_carrier N a L hperiod j))

def fs4PeriodicFourierFiniteSourceCoefficientMapH4 (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (c : Fin (Fintype.card (FinLatticeSites 4 N)) → ℝ) : FS4HminusFourCompletion :=
  ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
    c j • fs4PeriodicFourierSiteVectorH4 N a L hperiod j

theorem continuous_fs4PeriodicFourierFiniteSourceCoefficientMapH4
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L) :
    Continuous (fs4PeriodicFourierFiniteSourceCoefficientMapH4 N a L hperiod) := by
  unfold fs4PeriodicFourierFiniteSourceCoefficientMapH4
  exact continuous_finsetSum Finset.univ (fun j _ =>
    (continuous_apply j).smul continuous_const)

def fs4PeriodicFourierFiniteSourceCarrierLiftH4 (N : ℕ) [NeZero N]
    (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    FS4HminusFourCompletion :=
  fs4PeriodicFourierFiniteSourceCoefficientMapH4 N a L hperiod
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 4 N))))

theorem measurable_fs4PeriodicFourierFiniteSourceCarrierLiftH4
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L) :
    Measurable (fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod) := by
  unfold fs4PeriodicFourierFiniteSourceCarrierLiftH4
  have hcoords : Measurable (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 4 N)) =>
        fun j : Fin (Fintype.card (FinLatticeSites 4 N)) =>
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 4 N)))) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 4 N)))).comp (comap_measurable _)
  exact (continuous_fs4PeriodicFourierFiniteSourceCoefficientMapH4 N a L hperiod).measurable.comp hcoords

theorem fs4PeriodicFourierFiniteSourceCarrierLiftH4_apply
    (N : ℕ) [NeZero N] (a L : ℝ) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (k : FS4Index) :
    fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω k =
      ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 4 N))) : ℂ) *
          ((Real.sqrt (fs4SobolevWeight 4 k) : ℂ) *
            fs4PeriodicFourierSiteSequence N a L hperiod j k) := by
  change (⇑(fs4PeriodicFourierFiniteSourceCoefficientMapH4 N a L hperiod
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 4 N))))) k) = _
  rw [fs4PeriodicFourierFiniteSourceCoefficientMapH4, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    fs4PeriodicFourierSiteVectorH4, fs4HminusFourEmbeddingOfCoefficients,
    fs4WeightedFourierCoefficients, Complex.real_smul]

theorem fs4PeriodicFourierFiniteSourceCarrierLiftH4_eq_weightedRaw
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (k : FS4Index) :
    fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω k =
      (Real.sqrt (fs4SobolevWeight 4 k) : ℂ) *
        fs4PeriodicComplexFourierLift N a L hperiod ω k := by
  rw [fs4PeriodicFourierFiniteSourceCarrierLiftH4_apply,
    fs4PeriodicComplexFourierLift_eq_siteSum N a L ha hperiod ω]
  calc
    _ = ∑ j, (Real.sqrt (fs4SobolevWeight 4 k) : ℂ) *
        ((ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 4 N))) : ℂ) *
          fs4PeriodicFourierSiteSequence N a L hperiod j k) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [Finset.mul_sum]

theorem fs4PeriodicFourierFiniteSourceCarrierLiftH4_mem_realCarrier
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω ∈
      fs4HminusFourRealCarrier := by
  intro k
  rw [fs4PeriodicFourierFiniteSourceCarrierLiftH4_eq_weightedRaw
      N a L ha hperiod ω (fun i => -k i),
    fs4PeriodicFourierFiniteSourceCarrierLiftH4_eq_weightedRaw
      N a L ha hperiod ω k]
  rw [fs4SobolevWeight_neg]
  have hstar := fs4PeriodicComplexFourierLift_star_neg N a L ha hperiod ω k
  rw [← hstar]
  simp
def fs4PeriodicFourierFiniteSourceHminusFourMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) : Measure FS4HminusFourCompletion :=
  (finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 4 N a mass ha hmass)).map
      (fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod)

instance fs4PeriodicFourierFiniteSourceHminusFourMeasure_isProbabilityMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    IsProbabilityMeasure
      (fs4PeriodicFourierFiniteSourceHminusFourMeasure N a mass L
        ha hmass hL hperiod) := by
  unfold fs4PeriodicFourierFiniteSourceHminusFourMeasure
  apply map_preserves_probability
  exact (measurable_fs4PeriodicFourierFiniteSourceCarrierLiftH4
    N a L hperiod).aemeasurable

def fs4PeriodicFourierFiniteSourceHminusFourProbabilityMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) : ProbabilityMeasure FS4HminusFourCompletion :=
  ⟨fs4PeriodicFourierFiniteSourceHminusFourMeasure N a mass L
    ha hmass hL hperiod, inferInstance⟩

theorem fs4PeriodicFourierFiniteSourceCarrierLiftH4_norm_sq
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    ‖fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω‖ ^ 2 =
      ∑' k : FS4Index, fs4SobolevWeight 4 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal)
    (fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω)
  norm_num at hnorm
  rw [hnorm]
  apply tsum_congr
  intro k
  rw [fs4PeriodicFourierFiniteSourceCarrierLiftH4_eq_weightedRaw
    N a L ha hperiod ω k]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt (fs4SobolevWeight_nonneg 4 k)]


theorem fs4PeriodicFourierFiniteSourceCarrierLiftH4_norm_sq_le_H3
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    ‖fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω‖ ^ 2 ≤
      ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ^ 2 := by
  rw [fs4PeriodicFourierFiniteSourceCarrierLiftH4_norm_sq N a L ha hperiod ω,
    fs4PeriodicFourierFiniteSourceCarrierLift_norm_sq N a L ha hperiod ω]
  let b : FS4Index → ℝ := fun k =>
    ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
  have hb : Summable (fun k : FS4Index => fs4SobolevWeight 3 k * b k) := by
    exact fs4PeriodicComplexFourierLift_mem_carrier N a L ha hperiod ω
  have h4 : Summable (fun k : FS4Index => fs4SobolevWeight 4 k * b k) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (fs4SobolevWeight_nonneg 4 k) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right (fs4_weight_four_le_three k) (sq_nonneg _)) hb
  exact h4.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right (fs4_weight_four_le_three k) (sq_nonneg _)) hb

theorem fs4PeriodicFourierFiniteSourceCarrierLiftH4_integral_tsum_eq_weighted_trace
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    ∑' k : FS4Index, ∫ ω, fs4SobolevWeight 4 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 4 N a mass ha hmass) =
      ∫ ω, ∑' k : FS4Index, fs4SobolevWeight 4 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
      ∂finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 4 N a mass ha hmass) := by
  let T := numberedLatticeCovarianceGJ 4 N a mass ha hmass
  change (∑' k : FS4Index, ∫ ω, fs4SobolevWeight 4 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2 ∂finiteCovarianceGaussianMeasure T) =
      ∫ ω, ∑' k : FS4Index, fs4SobolevWeight 4 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2 ∂finiteCovarianceGaussianMeasure T
  apply integral_tsum_of_summable_integral_norm
  · intro k
    let fc := latticeTestField (physicalTestEval 4 N a)
      (periodicCosineTest 4 L k hperiod)
    let fs := latticeTestField (physicalTestEval 4 N a)
      (periodicSineTest 4 L k hperiod)
    have hcosLaw := finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T fc
    have hsinLaw := finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T fs
    have hcosInt : Integrable (fun ω => (ω fc) ^ 2)
        (finiteCovarianceGaussianMeasure T) := hcosLaw.memLp_two.integrable_sq
    have hsinInt : Integrable (fun ω => (ω fs) ^ 2)
        (finiteCovarianceGaussianMeasure T) := hsinLaw.memLp_two.integrable_sq
    have hadd := hcosInt.add hsinInt
    have hp : Integrable (fun ω => ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2)
        (finiteCovarianceGaussianMeasure T) := by
      apply hadd.congr
      filter_upwards [] with ω
      rw [fs4PeriodicComplexFourierLift_apply, fs4PeriodicComplexFourierProbe_norm_sq]
      rw [latticeEmbedLift_eval_eq, latticeEmbedLift_eval_eq]
      rfl
    exact hp.const_mul (fs4SobolevWeight 4 k)
  · have htrace := fs4PeriodicComplexFourierProbe_weighted_trace_bound
      N a mass L ha hmass hL hperiod
    have hsum3 : Summable (fun k : FS4Index => fs4SobolevWeight 3 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) := htrace.1
    have hmoment : ∀ k : FS4Index, 0 ≤
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
      intro k
      unfold fs4PeriodicComplexFourierProbeMoment
      exact integral_nonneg (fun ω => sq_nonneg
        ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖)
    have hnonneg : ∀ k : FS4Index, 0 ≤ fs4SobolevWeight 4 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
      intro k
      exact mul_nonneg (fs4SobolevWeight_nonneg 4 k) (hmoment k)
    have hle : ∀ k : FS4Index, fs4SobolevWeight 4 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k ≤
        fs4SobolevWeight 3 k * fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
      intro k
      exact mul_le_mul_of_nonneg_right (fs4_weight_four_le_three k) (hmoment k)
    have hsum4 : Summable (fun k : FS4Index => fs4SobolevWeight 4 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) :=
      hsum3.of_nonneg_of_le hnonneg hle
    apply hsum4.congr
    intro k
    rw [← fs4PeriodicComplexFourierLift_integral_eq_probeMoment
      N a mass L ha hmass hperiod k]
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (fs4SobolevWeight_nonneg 4 k) (sq_nonneg _))]

theorem fs4PeriodicFourierFiniteSourceCarrierLiftH4_integral_norm_sq_le
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hL : a * (N : ℝ) = L)
    (hperiod : 0 < L) :
    ∫ ω, ‖fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω‖ ^ 2
      ∂finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 4 N a mass ha hmass) ≤
      (2 * (mass⁻¹ ^ 2 * L ^ 4)) * ∑' k : FS4Index,
        fs4SobolevWeight 3 k := by
  have hbridge := fs4PeriodicFourierFiniteSourceCarrierLiftH4_integral_tsum_eq_weighted_trace
    N a mass L ha hmass hL hperiod
  have htrace := fs4PeriodicComplexFourierProbe_weighted_trace_bound
    N a mass L ha hmass hL hperiod
  have hmoment : ∀ k : FS4Index, 0 ≤
      fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
    intro k
    unfold fs4PeriodicComplexFourierProbeMoment
    exact integral_nonneg (fun ω => sq_nonneg
      ‖fs4PeriodicComplexFourierProbe L hperiod k ω‖)
  have hle : ∀ k : FS4Index, fs4SobolevWeight 4 k *
      fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k ≤
      fs4SobolevWeight 3 k * fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
    intro k
    exact mul_le_mul_of_nonneg_right (fs4_weight_four_le_three k) (hmoment k)
  have hnonneg : ∀ k : FS4Index, 0 ≤ fs4SobolevWeight 4 k *
      fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
    intro k
    exact mul_nonneg (fs4SobolevWeight_nonneg 4 k) (hmoment k)
  have hsum4 : Summable (fun k : FS4Index => fs4SobolevWeight 4 k *
      fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) :=
    htrace.1.of_nonneg_of_le hnonneg hle
  have hseries : (∑' k : FS4Index, fs4SobolevWeight 4 k *
      fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k) ≤
      ∑' k : FS4Index, fs4SobolevWeight 3 k *
      fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k :=
    hsum4.tsum_le_tsum hle htrace.1
  calc
    ∫ ω, ‖fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω‖ ^ 2
        ∂finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 4 N a mass ha hmass) =
      ∫ ω, ∑' k : FS4Index, fs4SobolevWeight 4 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
        ∂finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 4 N a mass ha hmass) := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact (fs4PeriodicFourierFiniteSourceCarrierLiftH4_norm_sq
              N a L ha hperiod ω)
    _ = ∑' k : FS4Index, ∫ ω, fs4SobolevWeight 4 k *
        ‖fs4PeriodicComplexFourierLift N a L hperiod ω k‖ ^ 2
        ∂finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 4 N a mass ha hmass) := hbridge.symm
    _ = ∑' k : FS4Index, fs4SobolevWeight 4 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := by
          apply tsum_congr
          intro k
          rw [integral_const_mul]
          congr 1
          exact fs4PeriodicComplexFourierLift_integral_eq_probeMoment
            N a mass L ha hmass hperiod k
    _ ≤ ∑' k : FS4Index, fs4SobolevWeight 3 k *
        fs4PeriodicComplexFourierProbeMoment N a mass L ha hmass hperiod k := hseries
    _ ≤ (2 * (mass⁻¹ ^ 2 * L ^ 4)) * ∑' k : FS4Index,
        fs4SobolevWeight 3 k := htrace.2

theorem fs4PeriodicFourierFiniteSourceCarrierLiftH4_mem_hminusThreeBall_realSlice
    (N : ℕ) [NeZero N] (a L B : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (hB : fs4HminusThreeNorm (fs4PeriodicComplexFourierLift N a L hperiod ω) ≤ B) :
    fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω ∈
      fs4HminusThreeBallInHminusFour B ∩ fs4HminusFourRealCarrier := by
  let c := fs4PeriodicComplexFourierLift N a L hperiod ω
  have hc : c ∈ fs4HminusThreeCoefficientCarrier := by
    exact fs4PeriodicComplexFourierLift_mem_carrier N a L ha hperiod ω
  have hc4 := fs4_hminus3_coefficients_in_hminus4 c hc
  have heq : fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω =
      fs4HminusFourEmbeddingOfCoefficients c hc4 := by
    apply Subtype.ext
    funext k
    rw [fs4PeriodicFourierFiniteSourceCarrierLiftH4_eq_weightedRaw
      N a L ha hperiod ω k]
    rfl
  exact ⟨⟨c, hc, hB, heq⟩,
    fs4PeriodicFourierFiniteSourceCarrierLiftH4_mem_realCarrier
      N a L ha hperiod ω⟩

set_option maxHeartbeats 1000000 in
theorem fs4PeriodicFourierFiniteSourceCarrierLift_integrable_norm_sq
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) :
    Integrable (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)) =>
      ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ^ 2)
      (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ 4 N a mass ha hmass)) := by
  let T := numberedLatticeCovarianceGJ 4 N a mass ha hmass
  let μ := finiteCovarianceGaussianMeasure T
  have hcoord (j : Fin (Fintype.card (FinLatticeSites 4 N))) :
      MemLp (fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)) =>
        ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 4 N)))) 2 μ := by
    have hg := finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T
      (Pi.single j (1 : ℝ))
    exact hg.memLp_two
  have hsum : MemLp (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 4 N)) =>
      ∑ j : Fin (Fintype.card (FinLatticeSites 4 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 4 N))) : ℝ) •
          fs4PeriodicFourierSiteVector N a L hperiod j) 2 μ := by
    have hsum' : MemLp (∑ j ∈ (Finset.univ : Finset
        (Fin (Fintype.card (FinLatticeSites 4 N)))),
        fun ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)) =>
          (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 4 N))) : ℝ) •
            fs4PeriodicFourierSiteVector N a L hperiod j) 2 μ := by
      apply MeasureTheory.memLp_finsetSum'
      intro j hj
      have hconst : MemLp (fun _ : FiniteLatticeConfiguration
          (Fintype.card (FinLatticeSites 4 N)) =>
            fs4PeriodicFourierSiteVector N a L hperiod j) ⊤ μ := memLp_const _
      exact hconst.smul (hcoord j)
    convert hsum' using 1
    ext ω
    simp [Finset.sum_apply]
  change Integrable (fun ω : FiniteLatticeConfiguration
    (Fintype.card (FinLatticeSites 4 N)) =>
      ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ^ 2) μ
  have hmap : MemLp (fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod) 2 μ := by
    change MemLp (fun ω => fs4PeriodicFourierFiniteSourceCoefficientMap N a L hperiod
      (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
        (Fintype.card (FinLatticeSites 4 N)))) ) 2 μ
    unfold fs4PeriodicFourierFiniteSourceCoefficientMap
    convert hsum using 1
  exact hmap.integrable_norm_pow'

theorem fs4PeriodicFourierFiniteSourceCarrierLift_norm_eq_hminusThreeNorm
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :
    ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ =
      fs4HminusThreeNorm (fs4PeriodicComplexFourierLift N a L hperiod ω) := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  rw [fs4PeriodicFourierFiniteSourceCarrierLift_norm_sq N a L ha hperiod ω]
  rfl

theorem measurableSet_fs4PeriodicFourierFiniteSourceCarrierLift_hminusThreeNorm_le
    (N : ℕ) [NeZero N] (a L B : ℝ) (ha : 0 < a) (hperiod : 0 < L) :
    MeasurableSet {ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)) |
      fs4HminusThreeNorm (fs4PeriodicComplexFourierLift N a L hperiod ω) ≤ B} := by
  have hset :
      {ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)) |
        fs4HminusThreeNorm (fs4PeriodicComplexFourierLift N a L hperiod ω) ≤ B} =
      {ω | ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ≤ B} := by
    ext ω
    change fs4HminusThreeNorm (fs4PeriodicComplexFourierLift N a L hperiod ω) ≤ B ↔
      ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ≤ B
    rw [← fs4PeriodicFourierFiniteSourceCarrierLift_norm_eq_hminusThreeNorm
      N a L ha hperiod ω]
  rw [hset]
  exact measurableSet_le
    ((measurable_fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod).norm)
    measurable_const

set_option maxHeartbeats 1000000 in
theorem fs4PeriodicFourierFiniteSourceCarrierLift_markov_tail
    (N : ℕ) [NeZero N] (a mass L B : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) (hB : 0 < B) :
    finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 4 N a mass ha hmass)
      {ω | B ^ 2 ≤ ‖fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod ω‖ ^ 2} ≤
      ENNReal.ofReal ((2 * (mass⁻¹ ^ 2 * L ^ 4) *
        ∑' k : FS4Index, fs4SobolevWeight 3 k) / B ^ 2) := by
  let μ := finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 4 N a mass ha hmass)
  let X := fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod
  have hInt := fs4PeriodicFourierFiniteSourceCarrierLift_integrable_norm_sq
    N a mass L ha hmass hperiod
  have hSecond := fs4PeriodicFourierFiniteSourceCarrierLift_integral_norm_sq_le
    N a mass L ha hmass hL hperiod
  have hScaled : Integrable (fun ω => ‖X ω‖ ^ 2 / B ^ 2) μ := by
    have hmul := hInt.const_mul ((B ^ 2)⁻¹)
    convert hmul using 1
    ext ω
    simp [X, div_eq_mul_inv, mul_comm]
  have hNonneg : 0 ≤ᵐ[μ] (fun ω => ‖X ω‖ ^ 2 / B ^ 2) := by
    filter_upwards [] with ω
    exact div_nonneg (sq_nonneg ‖X ω‖) (sq_nonneg B)
  let s : Set (FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) :=
    {ω | B ^ 2 ≤ ‖X ω‖ ^ 2}
  have hMarkov := hScaled.measure_le_integral hNonneg (s := s)
    (by
      intro ω hω
      dsimp [s] at hω ⊢
      exact (le_div_iff₀ (sq_pos_of_pos hB)).2 (by simpa using hω))
  have hIntegral : (∫ ω, ‖X ω‖ ^ 2 / B ^ 2 ∂μ) ≤
      (2 * (mass⁻¹ ^ 2 * L ^ 4) * ∑' k : FS4Index, fs4SobolevWeight 3 k) / B ^ 2 := by
    have hscale : (∫ ω, ‖X ω‖ ^ 2 / B ^ 2 ∂μ) =
        (B ^ 2)⁻¹ * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
      rw [show (fun ω => ‖X ω‖ ^ 2 / B ^ 2) =
        (fun ω => (B ^ 2)⁻¹ * ‖X ω‖ ^ 2) by
          funext ω
          ring]
      rw [integral_const_mul]
    rw [hscale]
    calc
      (B ^ 2)⁻¹ * ∫ ω, ‖X ω‖ ^ 2 ∂μ ≤
          (B ^ 2)⁻¹ * ((2 * (mass⁻¹ ^ 2 * L ^ 4)) *
            ∑' k : FS4Index, fs4SobolevWeight 3 k) :=
        mul_le_mul_of_nonneg_left hSecond (inv_nonneg.mpr (sq_nonneg B))
      _ = (2 * (mass⁻¹ ^ 2 * L ^ 4) *
          ∑' k : FS4Index, fs4SobolevWeight 3 k) / B ^ 2 := by ring
  have hOfReal := ENNReal.ofReal_le_ofReal hIntegral
  change μ s ≤ _ at hMarkov
  rw [show μ = finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 4 N a mass ha hmass) by rfl] at hMarkov
  exact hMarkov.trans hOfReal

set_option maxHeartbeats 1000000 in
theorem fs4PeriodicFourierFiniteSourceHminusFourMeasure_compactTail
    (N : ℕ) [NeZero N] (a mass L B : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (hperiod : 0 < L) (hB : 0 < B) :
    fs4PeriodicFourierFiniteSourceHminusFourMeasure N a mass L ha hmass hL hperiod
      (closure (fs4HminusThreeBallInHminusFour B ∩ fs4HminusFourRealCarrier))ᶜ ≤
      ENNReal.ofReal ((2 * (mass⁻¹ ^ 2 * L ^ 4) *
        ∑' k : FS4Index, fs4SobolevWeight 3 k) / B ^ 2) := by
  let μ := finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 4 N a mass ha hmass)
  let X := fs4PeriodicFourierFiniteSourceCarrierLift N a L hperiod
  let Y := fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod
  let K : Set FS4HminusFourCompletion :=
    closure (fs4HminusThreeBallInHminusFour B ∩ fs4HminusFourRealCarrier)
  have hKcompact : IsCompact K := by
    exact isCompact_closure_fs4HminusThreeRealSlice B hB.le
  have hKmeas : MeasurableSet Kᶜ := (hKcompact.isClosed.measurableSet).compl
  have hmap : Measurable Y := measurable_fs4PeriodicFourierFiniteSourceCarrierLiftH4
    N a L hperiod
  have hpre : Y ⁻¹' Kᶜ ⊆ {ω | B ^ 2 ≤ ‖X ω‖ ^ 2} := by
    intro ω hω
    by_contra htail
    have hnorm_lt : ‖X ω‖ < B := by
      have hsquare : ‖X ω‖ ^ 2 < B ^ 2 := lt_of_not_ge htail
      nlinarith [norm_nonneg (X ω), sq_nonneg (‖X ω‖ - B)]
    have hraw : fs4HminusThreeNorm (fs4PeriodicComplexFourierLift N a L hperiod ω) ≤ B := by
      rw [← fs4PeriodicFourierFiniteSourceCarrierLift_norm_eq_hminusThreeNorm
        N a L ha hperiod ω]
      exact hnorm_lt.le
    have hin := fs4PeriodicFourierFiniteSourceCarrierLiftH4_mem_hminusThreeBall_realSlice
      N a L B ha hperiod ω hraw
    have hclosure : Y ω ∈ K := subset_closure hin
    exact hω hclosure
  have hmapMeasure :
      fs4PeriodicFourierFiniteSourceHminusFourMeasure N a mass L ha hmass hL hperiod Kᶜ =
        μ (Y ⁻¹' Kᶜ) := by
    rw [fs4PeriodicFourierFiniteSourceHminusFourMeasure]
    exact Measure.map_apply hmap hKmeas
  rw [hmapMeasure]
  have htail := fs4PeriodicFourierFiniteSourceCarrierLift_markov_tail
    N a mass L B ha hmass hL hperiod hB
  exact (measure_mono hpre).trans htail

def fs4PeriodicFixedVolumeProbabilityMeasure
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    ProbabilityMeasure FS4HminusFourCompletion := by
  let N := n + 1
  let a : ℝ := L / ((n + 1 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hNa : a * (N : ℝ) = L := by
    dsimp [a, N]
    field_simp
  exact ⟨fs4PeriodicFourierFiniteSourceHminusFourMeasure N a mass L ha hmass hNa hL,
    inferInstance⟩
theorem fs4PeriodicFixedVolumeProbabilityMeasureSet_tight
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    IsTightMeasureSet
      {ρ : Measure FS4HminusFourCompletion |
        ∃ n, ρ = (fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass n : Measure _) } := by
  refine (isTightMeasureSet_iff_exists_isCompact_measure_compl_le).2 ?_
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ρ hρ
    simp [htop]
  · have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    let er : ℝ := ε.toReal
    let C : ℝ := 2 * (mass⁻¹ ^ 2 * L ^ 4) *
      ∑' k : FS4Index, fs4SobolevWeight 3 k
    let D : ℝ := C + 1
    let B : ℝ := Real.sqrt (D / er)
    have hsum : 0 ≤ ∑' k : FS4Index, fs4SobolevWeight 3 k :=
      tsum_nonneg (fun k => fs4SobolevWeight_nonneg 3 k)
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hD : 0 < D := by dsimp [D]; linarith
    have her : 0 < er := hεreal
    have hB : 0 < B := by
      dsimp [B]
      exact Real.sqrt_pos.2 (div_pos hD her)
    refine ⟨closure (fs4HminusThreeBallInHminusFour B ∩ fs4HminusFourRealCarrier),
      isCompact_closure_fs4HminusThreeRealSlice B hB.le, ?_⟩
    intro ρ hρ
    rcases hρ with ⟨n, rfl⟩
    dsimp [fs4PeriodicFixedVolumeProbabilityMeasure]
    let N := n + 1
    let a : ℝ := L / ((n + 1 : ℕ) : ℝ)
    have ha : 0 < a := by
      dsimp [a]
      exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
    have hNa : a * (N : ℝ) = L := by
      dsimp [a, N]
      field_simp
    have htail := fs4PeriodicFourierFiniteSourceHminusFourMeasure_compactTail
      N a mass L B ha hmass hNa hL hB
    rw [← ENNReal.ofReal_toReal htop]
    have hBsq : B ^ 2 = D / er := by
      dsimp [B]
      rw [Real.sq_sqrt (le_of_lt (div_pos hD her))]
    have hreal : C / B ^ 2 ≤ er := by
      rw [hBsq]
      dsimp [D]
      have her0 : 0 ≤ er := her.le
      have hden : 0 < C + 1 := by linarith
      apply (div_le_iff₀ (div_pos (by linarith : 0 < C + 1) her)).2
      field_simp
      nlinarith
    exact htail.trans (ENNReal.ofReal_le_ofReal hreal)
theorem fs4PeriodicFixedVolume_prokhorov_subsequence
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop) :
    ∃ (ms : ℕ → ℕ) (ν : ProbabilityMeasure FS4HminusFourCompletion),
      StrictMono ms ∧
      Tendsto
        (fun k => fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass (ns (ms k)))
        atTop (𝓝 ν) := by
  letI : TopologicalSpace.SeparableSpace FS4HminusFourCompletion :=
    fs4HminusFourCompletion_separable
  let μ : ℕ → ProbabilityMeasure FS4HminusFourCompletion :=
    fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass
  let S : Set (ProbabilityMeasure FS4HminusFourCompletion) := Set.range μ
  have htight : IsTightMeasureSet
      {ρ : Measure FS4HminusFourCompletion | ∃ n, ρ = (μ n : Measure _)} := by
    simpa [μ] using fs4PeriodicFixedVolumeProbabilityMeasureSet_tight L mass hL hmass
  have hcompact : IsCompact (closure S) := by
    apply isCompact_closure_of_isTightMeasureSet
    simpa [S, Set.ext_iff, eq_comm] using htight
  have hseq : ∀ n, μ (ns n) ∈ closure S := by
    intro n
    exact subset_closure ⟨ns n, rfl⟩
  obtain ⟨ν, _hνS, ms, hms, hlim⟩ := hcompact.tendsto_subseq hseq
  refine ⟨ms, ν, hms, ?_⟩
  simpa [Function.comp_def, μ] using hlim
def fs4HminusFourCoordinateCylinder
    (s : Finset FS4Index) (S : Set (∀ i : s, ℂ)) : Set FS4HminusFourCompletion :=
  (fun x : FS4HminusFourCompletion => s.restrict (x : FS4Index → ℂ)) ⁻¹' S
def fs4HminusFourMeasurableCylinders : Set (Set FS4HminusFourCompletion) :=
  {A | ∃ t ∈ measurableCylinders (fun _ : FS4Index => ℂ),
    (fun x : FS4HminusFourCompletion => (x : FS4Index → ℂ)) ⁻¹' t = A}
theorem measurable_fs4HminusFour_coordinate_inclusion :
    Measurable (fun x : FS4HminusFourCompletion =>
      (x : FS4Index → ℂ)) := by
  rw [measurable_pi_iff]
  intro k
  exact (fs4HminusFour_coordinate_continuous k).measurable
theorem fs4HminusFour_cylinder_mem
    (s : Finset FS4Index) {S : Set (∀ i : s, ℂ)} (hS : MeasurableSet S) :
    fs4HminusFourCoordinateCylinder s S ∈ fs4HminusFourMeasurableCylinders := by
  refine ⟨cylinder s S, ?_, ?_⟩
  · rw [mem_measurableCylinders]
    exact ⟨s, S, hS, rfl⟩
  · rfl
theorem fs4HminusFour_norm_sq_sublevel_measurable_of_generated_cylinders
    (y : FS4HminusFourCompletion) (r : ℝ) :
    @MeasurableSet FS4HminusFourCompletion
      (MeasurableSpace.generateFrom fs4HminusFourMeasurableCylinders)
      {x | ‖x - y‖ ^ 2 < r} := by
  letI : MeasurableSpace FS4HminusFourCompletion :=
    MeasurableSpace.generateFrom fs4HminusFourMeasurableCylinders
  have hcoord : ∀ i : FS4Index, Measurable (fun x : FS4HminusFourCompletion => x i) := by
    intro i A hA
    let j : {k // k ∈ ({i} : Finset FS4Index)} := ⟨i, by simp⟩
    have hS : MeasurableSet {z : ∀ k : ({i} : Finset FS4Index), ℂ | z j ∈ A} :=
      hA.preimage (measurable_pi_apply j)
    have hcyl := fs4HminusFour_cylinder_mem ({i} : Finset FS4Index) hS
    have heq : Set.preimage (fun x : FS4HminusFourCompletion => x i) A =
        fs4HminusFourCoordinateCylinder {i} {z | z j ∈ A} := by
      ext x
      rfl
    rw [heq]
    exact MeasurableSpace.measurableSet_generateFrom hcyl
  have hsum : Measurable (fun x : FS4HminusFourCompletion =>
      ∑' i : FS4Index, ‖x i - y i‖ ^ 2) :=
    Measurable.tsum (fun i => ((hcoord i).sub measurable_const).norm.pow_const 2)
  have hnorm : Measurable (fun x : FS4HminusFourCompletion => ‖x - y‖ ^ 2) := by
    convert hsum using 1
    funext x
    simpa using (lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ENNReal).toReal) (x - y))
  exact measurableSet_Iio.preimage hnorm
def FS4CylinderBorelGenerationInput : Prop :=
  MeasurableSpace.generateFrom fs4HminusFourMeasurableCylinders =
    borel FS4HminusFourCompletion
open TopologicalSpace in
theorem fs4HminusFour_cylinder_borel_generation : FS4CylinderBorelGenerationInput := by
  letI : TopologicalSpace.SeparableSpace FS4HminusFourCompletion :=
    fs4HminusFourCompletion_separable
  haveI : SecondCountableTopology FS4HminusFourCompletion := inferInstance
  change MeasurableSpace.generateFrom fs4HminusFourMeasurableCylinders =
    borel FS4HminusFourCompletion
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨t, ht, rfl⟩
    rw [mem_measurableCylinders] at ht
    rcases ht with ⟨s, S, hS, rfl⟩
    exact hS.preimage ((Finset.measurable_restrict s).comp
      measurable_fs4HminusFour_coordinate_inclusion)
  · letI : MeasurableSpace FS4HminusFourCompletion :=
      MeasurableSpace.generateFrom fs4HminusFourMeasurableCylinders
    have hball (y : FS4HminusFourCompletion) (r : ℝ) (hr : 0 < r) :
        MeasurableSet (Metric.ball y r) := by
      have heq : Metric.ball y r = {x | ‖x - y‖ ^ 2 < r ^ 2} := by
        ext x
        simp only [Metric.mem_ball, dist_eq_norm, Set.mem_setOf_eq]
        constructor <;> intro h <;> nlinarith [norm_nonneg (x - y)]
      rw [heq]
      exact fs4HminusFour_norm_sq_sublevel_measurable_of_generated_cylinders y (r ^ 2)
    apply MeasurableSpace.generateFrom_le
    intro U hU
    change IsOpen U at hU
    let F : Set (Set FS4HminusFourCompletion) :=
      {V | ∃ y r, 0 < r ∧ V = Metric.ball y r ∧ V ⊆ U}
    have hFopen : ∀ V ∈ F, IsOpen V := by
      rintro V ⟨y, r, hr, rfl, hsub⟩
      exact Metric.isOpen_ball
    have hFcover : ⋃₀ F = U := by
      ext x
      constructor
      · rintro ⟨V, ⟨y, r, hr, rfl, hsub⟩, hx⟩
        exact hsub hx
      · intro hx
        obtain ⟨r, hr, hsub⟩ :=
          (Metric.isOpen_iff (α := FS4HminusFourCompletion)).mp hU x hx
        exact Set.mem_sUnion.mpr
          ⟨Metric.ball x r, ⟨x, r, hr, rfl, hsub⟩, Metric.mem_ball_self hr⟩
    obtain ⟨v, hv, hvF, hvcover⟩ := isOpen_sUnion_countable F hFopen
    rw [← hFcover, ← hvcover]
    apply MeasurableSet.sUnion hv
    intro V hV
    rcases hvF hV with ⟨y, r, hr, rfl, hsub⟩
    exact hball y r hr
theorem fs4HminusFour_measure_ext_of_cylinder
    (μ ν : Measure FS4HminusFourCompletion)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : ∀ (s : Finset FS4Index) (S : Set (∀ i : s, ℂ)),
      MeasurableSet S →
        μ (fs4HminusFourCoordinateCylinder s S) =
          ν (fs4HminusFourCoordinateCylinder s S))
    (huniv : μ (Set.univ) = ν (Set.univ)) : μ = ν := by
  apply ext_of_generate_finite fs4HminusFourMeasurableCylinders
    fs4HminusFour_cylinder_borel_generation.symm
    (isPiSystem_measurableCylinders.comap
      (fun x : FS4HminusFourCompletion => (x : FS4Index → ℂ)))
  · intro A hA
    rcases hA with ⟨t, ht, rfl⟩
    rcases (mem_measurableCylinders t).mp ht with ⟨s, S, hS, rfl⟩
    exact hμν s S hS
  · simpa using huniv

theorem fs4HminusFour_probabilityMeasure_ext_of_finite_marginals
    (μ ν : ProbabilityMeasure FS4HminusFourCompletion)
    (hmarg : ∀ (s : Finset FS4Index),
      μ.map (fun x : FS4HminusFourCompletion =>
        s.restrict (x : FS4Index → ℂ)) =
      ν.map (fun x : FS4HminusFourCompletion =>
        s.restrict (x : FS4Index → ℂ))) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply fs4HminusFour_measure_ext_of_cylinder (μ := μ) (ν := ν)
  · intro s S hS
    have hmeas : Measurable (fun x : FS4HminusFourCompletion =>
        s.restrict (x : FS4Index → ℂ)) :=
      (Finset.measurable_restrict s).comp
        measurable_fs4HminusFour_coordinate_inclusion
    change (μ : Measure FS4HminusFourCompletion)
        (fs4HminusFourCoordinateCylinder s S) =
      (ν : Measure FS4HminusFourCompletion)
        (fs4HminusFourCoordinateCylinder s S)
    rw [fs4HminusFourCoordinateCylinder]
    rw [← Measure.map_apply hmeas hS, ← Measure.map_apply hmeas hS]
    exact congrArg
      (fun ρ : ProbabilityMeasure (∀ i : s, ℂ) =>
        (ρ : Measure (∀ i : s, ℂ)) S) (hmarg s)
  · simp [ProbabilityMeasure.coeFn_def]
/-- The zero-mode cosine covariance is exactly evaluated in the continuum Green pairing. -/
theorem fs4PeriodicResolvent_zeroCosine_pairing
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    (torusFourierGreenPairing 4 L mass
      (periodicCosineTest 4 L 0 hL) (periodicCosineTest 4 L 0 hL)).re =
        (((L : ℂ) ^ 4 / (mass : ℂ) ^ 2).re) := by
  have hper : IsFlatTorusPeriodic 4 L (periodicCosineTest 4 L 0 hL) :=
    periodicCosineTest_isFlatTorusPeriodic 4 L hL 0
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
    4 L mass hL hmass (periodicCosineTest 4 L 0 hL)
    (periodicCosineTest 4 L 0 hL) hper hper
  have hconst : ∀ n : ℕ,
      fixedVolumeCovarianceInner 4 L mass hL hmass
        (periodicCosineTest 4 L 0 hL) (periodicCosineTest 4 L 0 hL) n =
        (((L : ℂ) ^ 4 / (mass : ℂ) ^ 2).re) := by
    intro n
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    rw [discreteFourierGreenPairing_periodicCosineTest] <;> try exact hmass
    have hself : integerLatticeMode 4 (n + 1) 0 = -integerLatticeMode 4 (n + 1) 0 := by
      ext i
      simp [integerLatticeMode]
    rw [if_pos hself]
    have hs : fixedVolumeMassSymbol 4 (n + 1) L mass
        (integerLatticeMode 4 (n + 1) 0) = (mass : ℂ) ^ 2 := by
      rw [fixedVolumeMassSymbol_eq_real]
      simp [fixedVolumeMassSymbolReal, integerLatticeMode]
    rw [hs]
  have hconstlim : Filter.Tendsto
      (fun _ : ℕ => (((L : ℂ) ^ 4 / (mass : ℂ) ^ 2).re)) Filter.atTop
      (nhds (((L : ℂ) ^ 4 / (mass : ℂ) ^ 2).re)) := tendsto_const_nhds
  have heq := tendsto_nhds_unique
    (hlim.congr' (Filter.Eventually.of_forall hconst)) hconstlim
  exact heq
/-- The zero-mode sine coordinate vanishes in the continuum Green pairing. -/
theorem fs4PeriodicResolvent_zeroSine_pairing
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    (torusFourierGreenPairing 4 L mass
      (periodicSineTest 4 L 0 hL) (periodicSineTest 4 L 0 hL)).re = 0 := by
  have hper : IsFlatTorusPeriodic 4 L (periodicSineTest 4 L 0 hL) :=
    periodicSineTest_isFlatTorusPeriodic 4 L hL 0
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
    4 L mass hL hmass (periodicSineTest 4 L 0 hL)
    (periodicSineTest 4 L 0 hL) hper hper
  have hconst : ∀ n : ℕ,
      fixedVolumeCovarianceInner 4 L mass hL hmass
        (periodicSineTest 4 L 0 hL) (periodicSineTest 4 L 0 hL) n = 0 := by
    intro n
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    rw [discreteFourierGreenPairing_periodicSineTest] <;> try exact hmass
    have hself : integerLatticeMode 4 (n + 1) 0 = -integerLatticeMode 4 (n + 1) 0 := by
      ext i
      simp [integerLatticeMode]
    rw [if_pos hself]
    rfl
  have hconstlim : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique
    (hlim.congr' (Filter.Eventually.of_forall hconst)) hconstlim
  exact heq
theorem integerLatticeMode_eventually_ne_neg (k : Fin 4 → ℤ) (hk : ∃ i, k i ≠ 0) : ∀ᶠ n in Filter.atTop, integerLatticeMode 4 (n + 1) k ≠ -integerLatticeMode 4 (n + 1) k := by
  obtain ⟨i, hki⟩ := hk
  filter_upwards [eventually_gt_atTop (2 * (k i).natAbs)] with n hn
  intro hself
  have hzi : (k i : ZMod (n + 1)) = -(k i : ZMod (n + 1)) := by exact congrFun hself i
  have hzero : ((2 * k i : ℤ) : ZMod (n + 1)) = 0 := by
    push_cast
    simpa [two_mul] using (add_eq_zero_iff_eq_neg).2 hzi
  have hdiv : ((n + 1 : ℕ) : ℤ) ∣ 2 * k i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  have hdivabs : ((n + 1 : ℕ) : ℤ) ∣ |2 * k i| := (dvd_abs _ _).2 hdiv
  have habspos : 0 < |2 * k i| := by rw [abs_pos]; exact mul_ne_zero (by norm_num) hki
  have hbound := Int.le_of_dvd habspos hdivabs
  have hncast : (2 * (k i).natAbs : ℤ) < (n : ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hncast
  have habsEq : |2 * k i| = 2 * |k i| := by simp [abs_mul]
  rw [habsEq] at hbound
  omega
theorem fs4_nonzero_cosine_pairing_test (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (k : Fin 4 → ℤ) (hk : ∃ i, k i ≠ 0) :
    (torusFourierGreenPairing 4 L mass (periodicCosineTest 4 L k hL) (periodicCosineTest 4 L k hL)).re = ((((L : ℂ) ^ 4 / (torusMassSymbol 4 L mass k : ℂ)) / 2).re) := by
  have hper : IsFlatTorusPeriodic 4 L (periodicCosineTest 4 L k hL) := periodicCosineTest_isFlatTorusPeriodic 4 L hL k
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 4 L mass hL hmass (periodicCosineTest 4 L k hL) (periodicCosineTest 4 L k hL) hper hper
  have hnonself : ∀ᶠ n in Filter.atTop, integerLatticeMode 4 (n + 1) k ≠ -integerLatticeMode 4 (n + 1) k := integerLatticeMode_eventually_ne_neg k hk
  have hseq : ∀ᶠ n in Filter.atTop, fixedVolumeCovarianceInner 4 L mass hL hmass (periodicCosineTest 4 L k hL) (periodicCosineTest 4 L k hL) n = (((L : ℂ) ^ 4 / fixedVolumeMassSymbol 4 (n + 1) L mass (integerLatticeMode 4 (n + 1) k)) / 2).re := by
    filter_upwards [hnonself] with n hn
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    rw [discreteFourierGreenPairing_periodicCosineTest] <;> try exact hmass
    rw [if_neg hn]
  have hden := fixedVolumeMassSymbol_integerLatticeMode_tendsto 4 L mass k
  have hden0 : (torusMassSymbol 4 L mass k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (torusMassSymbol_pos 4 L mass hmass k).ne'
  have hnum : Filter.Tendsto (fun _ : ℕ => (L : ℂ) ^ 4) Filter.atTop (nhds ((L : ℂ) ^ 4)) := tendsto_const_nhds
  have hquot : Filter.Tendsto (fun n : ℕ => (((L : ℂ) ^ 4 / fixedVolumeMassSymbol 4 (n + 1) L mass (integerLatticeMode 4 (n + 1) k)) / 2)) Filter.atTop (nhds ((((L : ℂ) ^ 4 / (torusMassSymbol 4 L mass k : ℂ)) / 2))) := by
    simpa using (hnum.div hden hden0).div_const (2 : ℂ)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hquot
  have hlimquot : Filter.Tendsto (fun n : ℕ => (((L : ℂ) ^ 4 / fixedVolumeMassSymbol 4 (n + 1) L mass (integerLatticeMode 4 (n + 1) k)) / 2).re) Filter.atTop (nhds ((((L : ℂ) ^ 4 / (torusMassSymbol 4 L mass k : ℂ)) / 2).re)) := by
    convert hreal using 1
    · ext n
      rfl
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hlimquot
  exact heq
theorem fs4_nonzero_sine_pairing_test
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k : Fin 4 → ℤ) (hk : ∃ i, k i ≠ 0) :
    (torusFourierGreenPairing 4 L mass
      (periodicSineTest 4 L k hL) (periodicSineTest 4 L k hL)).re =
      ((((L : ℂ) ^ 4 / (torusMassSymbol 4 L mass k : ℂ)) / 2).re) := by
  have hper : IsFlatTorusPeriodic 4 L (periodicSineTest 4 L k hL) :=
    periodicSineTest_isFlatTorusPeriodic 4 L hL k
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
    4 L mass hL hmass (periodicSineTest 4 L k hL)
    (periodicSineTest 4 L k hL) hper hper
  have hnonself : ∀ᶠ n in Filter.atTop,
      integerLatticeMode 4 (n + 1) k ≠ -integerLatticeMode 4 (n + 1) k :=
    integerLatticeMode_eventually_ne_neg k hk
  have hseq : ∀ᶠ n in Filter.atTop,
      fixedVolumeCovarianceInner 4 L mass hL hmass
        (periodicSineTest 4 L k hL) (periodicSineTest 4 L k hL) n =
      (((L : ℂ) ^ 4 / fixedVolumeMassSymbol 4 (n + 1) L mass
        (integerLatticeMode 4 (n + 1) k)) / 2).re := by
    filter_upwards [hnonself] with n hn
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    rw [discreteFourierGreenPairing_periodicSineTest] <;> try exact hmass
    rw [if_neg hn]
  have hden := fixedVolumeMassSymbol_integerLatticeMode_tendsto 4 L mass k
  have hden0 : (torusMassSymbol 4 L mass k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (torusMassSymbol_pos 4 L mass hmass k).ne'
  have hnum : Filter.Tendsto (fun _ : ℕ => (L : ℂ) ^ 4)
      Filter.atTop (nhds ((L : ℂ) ^ 4)) := tendsto_const_nhds
  have hquot : Filter.Tendsto
      (fun n : ℕ => (((L : ℂ) ^ 4 /
        fixedVolumeMassSymbol 4 (n + 1) L mass (integerLatticeMode 4 (n + 1) k)) / 2))
      Filter.atTop (nhds ((((L : ℂ) ^ 4 /
        (torusMassSymbol 4 L mass k : ℂ)) / 2))) := by
    simpa using (hnum.div hden hden0).div_const (2 : ℂ)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hquot
  have hlimquot : Filter.Tendsto
      (fun n : ℕ => (((L : ℂ) ^ 4 /
        fixedVolumeMassSymbol 4 (n + 1) L mass (integerLatticeMode 4 (n + 1) k)) / 2).re)
      Filter.atTop (nhds ((((L : ℂ) ^ 4 /
        (torusMassSymbol 4 L mass k : ℂ)) / 2).re)) := by
    convert hreal using 1
    · ext n
      rfl
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hlimquot
  exact heq
theorem integerLatticeMode_eventually_ne_of_ne (k l : Fin 4 → ℤ) (h : k ≠ l) :
    ∀ᶠ n in Filter.atTop, integerLatticeMode 4 (n + 1) k ≠ integerLatticeMode 4 (n + 1) l := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  filter_upwards [eventually_gt_atTop ((k i - l i).natAbs)] with n hn
  intro hres
  have hzero : ((k i - l i : ℤ) : ZMod (n + 1)) = 0 := by
    have hcoord := congrFun hres i
    change (k i : ZMod (n + 1)) = (l i : ZMod (n + 1)) at hcoord
    push_cast
    exact sub_eq_zero.mpr hcoord
  have hdiv : ((n + 1 : ℕ) : ℤ) ∣ k i - l i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  have habspos : 0 < |k i - l i| := by rw [abs_pos]; exact sub_ne_zero.mpr hi
  have hbound := Int.le_of_dvd habspos ((dvd_abs _ _).2 hdiv)
  have hncast : ((k i - l i).natAbs : ℤ) < (n : ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hncast
  omega
theorem integerLatticeMode_eventually_ne_neg_of_ne (k l : Fin 4 → ℤ) (h : k ≠ -l) :
    ∀ᶠ n in Filter.atTop, integerLatticeMode 4 (n + 1) k ≠ -integerLatticeMode 4 (n + 1) l := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have hi' : k i + l i ≠ 0 := by
    intro hz
    exact hi ((add_eq_zero_iff_eq_neg.mp hz))
  filter_upwards [eventually_gt_atTop ((k i + l i).natAbs)] with n hn
  intro hres
  have hzero : ((k i + l i : ℤ) : ZMod (n + 1)) = 0 := by
    have hcoord := congrFun hres i
    change (k i : ZMod (n + 1)) = -(l i : ZMod (n + 1)) at hcoord
    push_cast
    exact add_eq_zero_iff_eq_neg.mpr hcoord
  have hdiv : ((n + 1 : ℕ) : ℤ) ∣ k i + l i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  have habspos : 0 < |k i + l i| := by rw [abs_pos]; exact hi'
  have hbound := Int.le_of_dvd habspos ((dvd_abs _ _).2 hdiv)
  have hncast : ((k i + l i).natAbs : ℤ) < (n : ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hncast
  omega
theorem fs4_cosine_cross_disjoint_test (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin 4 → ℤ) (hkl : k ≠ l) (hknl : k ≠ -l) :
    (torusFourierGreenPairing 4 L mass (periodicCosineTest 4 L k hL) (periodicCosineTest 4 L l hL)).re = 0 := by
  have hperK := periodicCosineTest_isFlatTorusPeriodic 4 L hL k
  have hperL := periodicCosineTest_isFlatTorusPeriodic 4 L hL l
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 4 L mass hL hmass
    (periodicCosineTest 4 L k hL) (periodicCosineTest 4 L l hL) hperK hperL
  have hevents := (integerLatticeMode_eventually_ne_of_ne k l hkl).and
    (integerLatticeMode_eventually_ne_neg_of_ne k l hknl)
  have hseq : ∀ᶠ n in Filter.atTop, fixedVolumeCovarianceInner 4 L mass hL hmass
      (periodicCosineTest 4 L k hL) (periodicCosineTest 4 L l hL) n = 0 := by
    filter_upwards [hevents] with n hn
    rcases hn with ⟨h1, h2⟩
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    have h3 : -integerLatticeMode 4 (n + 1) k ≠ integerLatticeMode 4 (n + 1) l := by
      intro h
      apply h2
      simpa using congrArg Neg.neg h
    have h4 : -integerLatticeMode 4 (n + 1) k ≠ -integerLatticeMode 4 (n + 1) l := by
      intro h
      apply h1
      exact neg_injective h
    rw [discreteFourierGreenPairing_periodicCosineTest_disjoint]
    · rfl
    · exact hmass
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hzero
  exact heq

theorem fs4_sine_cross_disjoint_test (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin 4 → ℤ) (hkl : k ≠ l) (hknl : k ≠ -l) :
    (torusFourierGreenPairing 4 L mass (periodicSineTest 4 L k hL) (periodicSineTest 4 L l hL)).re = 0 := by
  have hperK := periodicSineTest_isFlatTorusPeriodic 4 L hL k
  have hperL := periodicSineTest_isFlatTorusPeriodic 4 L hL l
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 4 L mass hL hmass
    (periodicSineTest 4 L k hL) (periodicSineTest 4 L l hL) hperK hperL
  have hevents := (integerLatticeMode_eventually_ne_of_ne k l hkl).and
    (integerLatticeMode_eventually_ne_neg_of_ne k l hknl)
  have hseq : ∀ᶠ n in Filter.atTop, fixedVolumeCovarianceInner 4 L mass hL hmass
      (periodicSineTest 4 L k hL) (periodicSineTest 4 L l hL) n = 0 := by
    filter_upwards [hevents] with n hn
    rcases hn with ⟨h1, h2⟩
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    have h3 : -integerLatticeMode 4 (n + 1) k ≠ integerLatticeMode 4 (n + 1) l := by
      intro h; apply h2; simpa using congrArg Neg.neg h
    have h4 : -integerLatticeMode 4 (n + 1) k ≠ -integerLatticeMode 4 (n + 1) l := by
      intro h; apply h1; exact neg_injective h
    rw [discreteFourierGreenPairing_periodicSineTest_disjoint]
    · rfl
    · exact hmass
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hzero
  exact heq
theorem fs4_target_hminus4_trace_summable (L mass : ℝ) (hmass : 0 < mass) :
    Summable (fun k : FS4Index => fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k) := by
  have hmass2 : 0 < mass ^ 2 := sq_pos_of_pos hmass
  have hden (k : FS4Index) : mass ^ 2 ≤ torusMassSymbol 4 L mass k := by
    unfold torusMassSymbol
    have hsum : 0 ≤ ∑ i : Fin 4, (k i : ℝ) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hmul := mul_nonneg (sq_nonneg (2 * Real.pi / L)) hsum
    linarith
  have hbound (k : FS4Index) : fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k ≤
      (mass ^ 2)⁻¹ * fs4SobolevWeight 4 k := by
    have hdenpos : 0 < torusMassSymbol 4 L mass k := torusMassSymbol_pos 4 L mass hmass k
    have hinv : (torusMassSymbol 4 L mass k)⁻¹ ≤ (mass ^ 2)⁻¹ :=
      (inv_le_inv₀ hdenpos hmass2).2 (hden k)
    have hw := fs4SobolevWeight_nonneg 4 k
    calc
      fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k =
          fs4SobolevWeight 4 k * (torusMassSymbol 4 L mass k)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ fs4SobolevWeight 4 k * (mass ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv hw
      _ = (mass ^ 2)⁻¹ * fs4SobolevWeight 4 k := by ring
  apply Summable.of_nonneg_of_le
    (fun k => div_nonneg (fs4SobolevWeight_nonneg 4 k) (le_of_lt (torusMassSymbol_pos 4 L mass hmass k)))
    hbound
  simpa [mul_comm] using (fs4HMinusFourWeight_summable.mul_left ((mass ^ 2)⁻¹))

theorem fs4_target_hminus4_weighted_variance_summable (L mass : ℝ) (hmass : 0 < mass) :
    Summable (fun k : FS4Index => L ^ 4 * (fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k)) := by
  simpa only [mul_comm] using
    (fs4_target_hminus4_trace_summable L mass hmass).mul_left (L ^ 4)

theorem fs4_cosine_sine_cross_test (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (k l : Fin 4 → ℤ) :
    (torusFourierGreenPairing 4 L mass (periodicCosineTest 4 L k hL) (periodicSineTest 4 L l hL)).re = 0 := by
  have hperK := periodicCosineTest_isFlatTorusPeriodic 4 L hL k
  have hperL := periodicSineTest_isFlatTorusPeriodic 4 L hL l
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 4 L mass hL hmass (periodicCosineTest 4 L k hL) (periodicSineTest 4 L l hL) hperK hperL
  have hfinite (n : ℕ) : fixedVolumeCovarianceInner 4 L mass hL hmass (periodicCosineTest 4 L k hL) (periodicSineTest 4 L l hL) n = 0 := by
    letI : NeZero (n + 1) := ⟨(Nat.succ_pos n).ne'⟩
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    let q := integerLatticeMode 4 (n + 1) k
    let r := integerLatticeMode 4 (n + 1) l
    by_cases hqr : q = r
    · have hcoef (p : FinLatticeSites 4 (n + 1)) : sampledFourierCoefficient 4 (n + 1) L (periodicSineTest 4 L l hL) p = sampledFourierCoefficient 4 (n + 1) L (periodicSineTest 4 L k hL) p := by
        rw [sampledFourierCoefficient_periodicSineTest, sampledFourierCoefficient_periodicSineTest]
        simp [q, r, hqr] <;> ring
      have hdiag := discreteFourierGreenPairing_periodicCosineSineTest_sameMode 4 (n + 1) L mass hL hmass k
      unfold discreteFourierGreenPairing at hdiag ⊢
      simp_rw [hcoef]
      exact congrArg Complex.re hdiag
    · by_cases hqnr : q = -r
      · have hcoef (p : FinLatticeSites 4 (n + 1)) : sampledFourierCoefficient 4 (n + 1) L (periodicSineTest 4 L l hL) p = -sampledFourierCoefficient 4 (n + 1) L (periodicSineTest 4 L k hL) p := by
          rw [sampledFourierCoefficient_periodicSineTest, sampledFourierCoefficient_periodicSineTest]
          simp [q, r, hqnr] <;> ring
        have hdiag := discreteFourierGreenPairing_periodicCosineSineTest_sameMode 4 (n + 1) L mass hL hmass k
        unfold discreteFourierGreenPairing at hdiag ⊢
        simp_rw [hcoef]
        simp only [mul_neg, neg_div]
        have hsum := neg_eq_zero.mpr hdiag
        simpa only [Finset.sum_neg_distrib, mul_neg, Complex.neg_re, Complex.zero_re] using congrArg Complex.re hsum
      · have hnr : -q ≠ r := by intro hz; apply hqnr; simpa using congrArg Neg.neg hz
        have hnn : -q ≠ -r := by intro hz; apply hqr; exact neg_injective hz
        have hdis := discreteFourierGreenPairing_periodicCosineSineTest_disjoint 4 (n + 1) L mass hL hmass k l
          (by simpa [q, r] using hqr) (by simpa [q, r] using hqnr)
          (by simpa [q, r] using hnr) (by simpa [q, r] using hnn)
        exact congrArg Complex.re hdis
  have hseq : ∀ᶠ n in Filter.atTop, fixedVolumeCovarianceInner 4 L mass hL hmass (periodicCosineTest 4 L k hL) (periodicSineTest 4 L l hL) n = 0 := Filter.Eventually.of_forall hfinite
  have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hzero
  exact heq
end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

lemma fs4_torus_symbol_lower_bound (L mass : ℝ) (k : FS4Index) :
    (2 * Real.pi / L)^2 * (max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖)^2 ≤
      torusMassSymbol 4 L mass k := by
  have hg := fs4_split_norm_sq_le_energy k
  have hdiff : 0 ≤ (∑ i : Fin 4, (k i : ℝ)^2) -
      (max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖)^2 := sub_nonneg.mpr hg
  unfold torusMassSymbol
  nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi / L)) hdiff, sq_nonneg mass]

lemma fs4_sqrt_torus_symbol_lower_bound (L mass : ℝ) (hmass : 0 < mass)
    (k : FS4Index) :
    |2 * Real.pi / L| * max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖ ≤
      Real.sqrt (torusMassSymbol 4 L mass k) := by
  have hM : 0 ≤ max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖ := by positivity
  have hden : 0 < torusMassSymbol 4 L mass k := torusMassSymbol_pos 4 L mass hmass k
  apply (Real.le_sqrt (mul_nonneg (abs_nonneg (2 * Real.pi / L)) hM) hden.le).2
  have hs := fs4_torus_symbol_lower_bound L mass k
  simpa [sq_abs, mul_pow] using hs

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

theorem fs4_sqrt_weighted_resolvent_summable (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun k : FS4Index =>
      Real.sqrt (fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k)) := by
  let C : ℝ := 2 * (mass⁻¹ + |2 * Real.pi / L|⁻¹)
  have hα : 0 < |2 * Real.pi / L| :=
    abs_pos.mpr (ne_of_gt (div_pos (mul_pos (by norm_num) Real.pi_pos) hL))
  have hC : 0 < C := by dsimp [C]; positivity
  have hCm : 2 ≤ C * mass := by
    dsimp [C]
    field_simp [ne_of_gt hmass, ne_of_gt hα]
    linarith
  have hCα : 2 ≤ C * |2 * Real.pi / L| := by
    dsimp [C]
    field_simp [ne_of_gt hmass, ne_of_gt hα]
    linarith
  have hmajor := (fs4SobolevWeight_summable (5/2) (by norm_num)).mul_left C
  apply Summable.of_nonneg_of_le (fun k => Real.sqrt_nonneg _) ?_ hmajor
  intro k
  let M := max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖
  let B := 1 + M
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 < B := by dsimp [B]; linarith
  have hden : 0 < torusMassSymbol 4 L mass k :=
    torusMassSymbol_pos 4 L mass hmass k
  have hgeom := fs4_split_norm_sq_le_energy k
  have hdiff : 0 ≤ (∑ i : Fin 4, (k i : ℝ)^2) - M^2 :=
    by simpa [M] using sub_nonneg.mpr hgeom
  have hdenlow : mass^2 + (2 * Real.pi / L)^2 * M^2 ≤
      torusMassSymbol 4 L mass k := by
    unfold torusMassSymbol
    nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi / L)) hdiff]
  have hCm2 : 4 ≤ C^2 * mass^2 := by
    nlinarith [sq_nonneg (C * mass - 2)]
  have hCα2 : 4 ≤ C^2 * |2 * Real.pi / L|^2 := by
    have hαsq : |2 * Real.pi / L|^2 = (2 * Real.pi / L)^2 := sq_abs _
    rw [hαsq]
    nlinarith [sq_nonneg (C * |2 * Real.pi / L| - 2)]
  have hprod := mul_le_mul_of_nonneg_left hdenlow (sq_nonneg C)
  have htermM : 4 * M^2 ≤ C^2 * (2 * Real.pi / L)^2 * M^2 := by
    have ht := mul_le_mul_of_nonneg_right hCα2 (sq_nonneg M)
    simpa [sq_abs] using ht
  have hClower : (1 + M)^2 ≤ C^2 * torusMassSymbol 4 L mass k := by
    nlinarith [sq_nonneg (M - 1)]
  have hweight4 : fs4SobolevWeight 4 k = (B^8)⁻¹ := by
    simp only [fs4SobolevWeight]
    rw [show -2 * (4 : ℝ) = -8 by norm_num, Real.rpow_neg (le_of_lt hB)]
    simp [B, M]
  have hweight25 : fs4SobolevWeight (5/2 : ℝ) k = (B^5)⁻¹ := by
    simp only [fs4SobolevWeight]
    rw [show -2 * (5/2 : ℝ) = -5 by norm_num, Real.rpow_neg (le_of_lt hB)]
    simp [B, M]
  have hpow : (B^8)⁻¹ = ((B^5)⁻¹)^2 * B^2 := by
    field_simp [ne_of_gt hB]
  have hsq : Real.sqrt (fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k)^2 ≤
      (C * fs4SobolevWeight (5/2 : ℝ) k)^2 := by
    rw [Real.sq_sqrt (div_nonneg (fs4SobolevWeight_nonneg 4 k) hden.le), mul_pow,
      hweight4, hweight25, hpow]
    apply (div_le_iff₀ hden).2
    calc
      (B^5)⁻¹ ^ 2 * B^2 ≤ (B^5)⁻¹ ^ 2 * (C^2 * torusMassSymbol 4 L mass k) :=
        mul_le_mul_of_nonneg_left hClower (sq_nonneg ((B^5)⁻¹))
      _ = (C^2 * (B^5)⁻¹ ^ 2) * torusMassSymbol 4 L mass k := by ring
  have hnonneg : 0 ≤ Real.sqrt (fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k) :=
    Real.sqrt_nonneg _
  have hnonnegR : 0 ≤ C * fs4SobolevWeight (5/2 : ℝ) k :=
    mul_nonneg hC.le (fs4SobolevWeight_nonneg _ _)
  exact (sq_le_sq₀ hnonneg hnonnegR).mp hsq

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum


/-- A single weighted Fourier-coordinate vector with the cosine-scale coefficient. -/
def fs4GaussianCosDirection (L mass : ℝ) (k : FS4Index) : FS4HminusFourCompletion :=
  lp.single (E := fun _ : FS4Index => ℂ) 2 k
    ((((Real.sqrt (fs4SobolevWeight 4 k) *
      (L^2 / (2 * Real.sqrt (torusMassSymbol 4 L mass k)))) : ℝ) : ℂ))

theorem fs4GaussianCosDirection_norm (L mass : ℝ) (k : FS4Index) :
    ‖fs4GaussianCosDirection L mass k‖ =
      Real.sqrt (fs4SobolevWeight 4 k) *
        (L^2 / (2 * Real.sqrt (torusMassSymbol 4 L mass k))) := by
  rw [fs4GaussianCosDirection, lp.norm_single (by norm_num : 0 < (2 : ENNReal))]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (sq_nonneg L) (by positivity)))]

theorem fs4GaussianCosDirection_norm_le (L mass : ℝ) (hmass : 0 < mass)
    (k : FS4Index) :
    ‖fs4GaussianCosDirection L mass k‖ ≤
      L^2 * Real.sqrt (fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k) := by
  rw [fs4GaussianCosDirection_norm]
  have hd : 0 < torusMassSymbol 4 L mass k :=
    torusMassSymbol_pos 4 L mass hmass k
  have hs : 0 < Real.sqrt (torusMassSymbol 4 L mass k) :=
    Real.sqrt_pos.2 hd
  have hw : 0 ≤ fs4SobolevWeight 4 k :=
    fs4SobolevWeight_nonneg 4 k
  have hwS : 0 ≤ Real.sqrt (fs4SobolevWeight 4 k) :=
    Real.sqrt_nonneg _
  calc
    Real.sqrt (fs4SobolevWeight 4 k) *
        (L^2 / (2 * Real.sqrt (torusMassSymbol 4 L mass k))) =
      L^2 * (Real.sqrt (fs4SobolevWeight 4 k) /
        (2 * Real.sqrt (torusMassSymbol 4 L mass k))) := by ring
    _ ≤ L^2 * (Real.sqrt (fs4SobolevWeight 4 k) /
        Real.sqrt (torusMassSymbol 4 L mass k)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hwS (by positivity) (by linarith))
        (sq_nonneg L)
    _ = L^2 * Real.sqrt (fs4SobolevWeight 4 k /
        torusMassSymbol 4 L mass k) := by rw [Real.sqrt_div hw]

def fs4GaussianDirectionIndexEquiv :
    FS4Index × (Unit ⊕ Unit) ≃ FS4Index ⊕ FS4Index :=
  Equiv.prodSumDistrib FS4Index Unit Unit |>.trans
    (Equiv.sumCongr (Equiv.prodPUnit FS4Index)
      (Equiv.prodPUnit FS4Index))

theorem fs4GaussianDuplicateSummable (f : FS4Index → ℝ)
    (hf : Summable f) :
    Summable (fun q : FS4Index × (Unit ⊕ Unit) => f q.1) := by
  rw [show (fun q : FS4Index × (Unit ⊕ Unit) => f q.1) =
      (fun q : FS4Index ⊕ FS4Index => q.elim f f) ∘
        fs4GaussianDirectionIndexEquiv by
    funext q
    cases q with
    | mk k s => cases s <;> rfl]
  rw [Equiv.summable_iff fs4GaussianDirectionIndexEquiv]
  apply Summable.sum
  · simpa using hf
  · simpa using hf

theorem fs4GaussianCosDirection_norm_summable
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun q : FS4Index × (Unit ⊕ Unit) =>
      ‖fs4GaussianCosDirection L mass q.1‖) :=
  Summable.of_norm_bounded
    (fs4GaussianDuplicateSummable
      (fun k => L^2 * Real.sqrt
        (fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k))
      ((fs4_sqrt_weighted_resolvent_summable L mass hL hmass).mul_left (L^2)))
    (fun q => by
      simpa using fs4GaussianCosDirection_norm_le L mass hmass q.1)

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

def fs4GaussianSinCoordinateVector (L mass : ℝ) (k : FS4Index) : FS4HminusFourCompletion :=
  lp.single (E := fun _ : FS4Index => ℂ) 2 k
    (Complex.I * (((Real.sqrt (fs4SobolevWeight 4 k) *
      (L^2 / (2 * Real.sqrt (torusMassSymbol 4 L mass k)))) : ℝ) : ℂ))

theorem fs4GaussianSinCoordinateVector_norm (L mass : ℝ) (k : FS4Index) :
    ‖fs4GaussianSinCoordinateVector L mass k‖ =
      ‖fs4GaussianCosDirection L mass k‖ := by
  rw [fs4GaussianSinCoordinateVector, fs4GaussianCosDirection,
    lp.norm_single (by norm_num : 0 < (2 : ENNReal)),
    lp.norm_single (by norm_num : 0 < (2 : ENNReal))]
  simp [Complex.norm_mul]

theorem fs4GaussianSinCoordinateVector_norm_summable
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun q : FS4Index × (Unit ⊕ Unit) =>
      ‖fs4GaussianSinCoordinateVector L mass q.1‖) := by
  simpa only [fs4GaussianSinCoordinateVector_norm] using
    (fs4GaussianCosDirection_norm_summable L mass hL hmass)

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

def fs4GaussianZeroDirection (L mass : ℝ) : FS4HminusFourCompletion :=
  lp.single (E := fun _ : FS4Index => ℂ) 2 0 (((L^2 / mass : ℝ) : ℂ))

theorem fs4GaussianZeroDirection_norm (L mass : ℝ) (hmass : 0 < mass) :
    ‖fs4GaussianZeroDirection L mass‖ = L^2 / mass := by
  rw [fs4GaussianZeroDirection, lp.norm_single
    (by norm_num : 0 < (2 : ENNReal))]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (div_nonneg (sq_nonneg L) (le_of_lt hmass))

theorem fs4GaussianZeroDirection_summable (L mass : ℝ) (hmass : 0 < mass) :
    Summable (fun _ : Unit => ‖fs4GaussianZeroDirection L mass‖) := by
  exact Summable.of_finite

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

def fs4RealPairVector (k : FS4Index) (c : ℂ) :
    FS4HminusFourCompletion :=
  lp.single (E := fun _ : FS4Index => ℂ) 2 k c +
    lp.single (E := fun _ : FS4Index => ℂ) 2 (fun i => -k i) (star c)

theorem fs4RealPairVector_mem (k : FS4Index) (c : ℂ)
    (hne : (fun i => -k i) ≠ k) :
    fs4RealPairVector k c ∈ fs4HminusFourRealCarrier := by
  intro q
  by_cases hqk : q = k
  · subst q
    simp [fs4RealPairVector, lp.single_apply, hne]
  · by_cases hqnk : q = (fun i => -k i)
    · subst q
      simp [fs4RealPairVector, lp.single_apply, hne, Ne.symm hne]
    · have hqkn : (fun i => -q i) ≠ k := by
        intro h
        apply hqnk
        funext i
        have hi := congrFun h i
        have hj := congrArg Neg.neg hi
        simpa using hj
      have hqnn : (fun i => -q i) ≠ (fun i => -k i) := by
        intro h
        apply hqk
        funext i
        have hi := congrFun h i
        have hj := congrArg Neg.neg hi
        simpa using hj
      simp [fs4RealPairVector, lp.single_apply, hqk, hqnk, hqkn, hqnn]

theorem fs4RealPairVector_norm_le (k : FS4Index) (c : ℂ) :
    ‖fs4RealPairVector k c‖ ≤ 2 * ‖c‖ := by
  rw [fs4RealPairVector]
  calc
    ‖lp.single (E := fun _ : FS4Index => ℂ) 2 k c +
        lp.single (E := fun _ : FS4Index => ℂ) 2 (fun i => -k i) (star c)‖
        ≤ ‖lp.single (E := fun _ : FS4Index => ℂ) 2 k c‖ +
          ‖lp.single (E := fun _ : FS4Index => ℂ) 2 (fun i => -k i) (star c)‖ :=
      norm_add_le _ _
    _ = 2 * ‖c‖ := by
      rw [lp.norm_single (by norm_num : 0 < (2 : ENNReal)),
        lp.norm_single (by norm_num : 0 < (2 : ENNReal))]
      rw [norm_star]
      ring

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

def fs4RealCosinePairVector (k : FS4Index) (r : ℝ) :
    FS4HminusFourCompletion :=
  fs4RealPairVector k (r : ℂ)

def fs4RealSinePairVector (k : FS4Index) (r : ℝ) :
    FS4HminusFourCompletion :=
  fs4RealPairVector k (Complex.I * (r : ℂ))

theorem fs4RealCosinePairVector_mem (k : FS4Index) (r : ℝ)
    (hne : (fun i => -k i) ≠ k) :
    fs4RealCosinePairVector k r ∈ fs4HminusFourRealCarrier :=
  fs4RealPairVector_mem k (r : ℂ) hne

theorem fs4RealSinePairVector_mem (k : FS4Index) (r : ℝ)
    (hne : (fun i => -k i) ≠ k) :
    fs4RealSinePairVector k r ∈ fs4HminusFourRealCarrier :=
  fs4RealPairVector_mem k (Complex.I * (r : ℂ)) hne

theorem fs4RealCosinePairVector_norm_le (k : FS4Index) (r : ℝ) :
    ‖fs4RealCosinePairVector k r‖ ≤ 2 * |r| := by
  simpa [fs4RealCosinePairVector, Complex.norm_real, Real.norm_eq_abs] using
    (fs4RealPairVector_norm_le k (r : ℂ))

theorem fs4RealSinePairVector_norm_le (k : FS4Index) (r : ℝ) :
    ‖fs4RealSinePairVector k r‖ ≤ 2 * |r| := by
  have h := fs4RealPairVector_norm_le k (Complex.I * (r : ℂ))
  have hi : ‖Complex.I * (r : ℂ)‖ = |r| := by
    rw [Complex.norm_mul, Complex.norm_I, Complex.norm_real]
    simp
  simpa [fs4RealSinePairVector, hi] using h

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

def fs4FirstNonzeroPositive (k : FS4Index) : Prop :=
  ∃ j : Fin 4, (∀ i, i < j → k i = 0) ∧ 0 < k j

def fs4CanonicalPairRepresentative (k : FS4Index) : Prop :=
  k ≠ 0 ∧ fs4FirstNonzeroPositive k

theorem fs4FirstNonzeroPositive_or_neg (k : FS4Index) (hk : k ≠ 0) :
    fs4FirstNonzeroPositive k ∨
      fs4FirstNonzeroPositive (fun i => -k i) := by
  classical
  let s : Finset (Fin 4) := Finset.univ.filter (fun i => k i ≠ 0)
  have hs : s.Nonempty := by
    by_contra h
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hzero : ∀ i : Fin 4, k i = 0 := by
      intro i
      by_contra hi
      have hiS : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hempty] at hiS
      simp at hiS
    apply hk
    funext i
    exact hzero i
  let j := s.min' hs
  have hjmem : j ∈ s := Finset.min'_mem s hs
  have hjne : k j ≠ 0 := (Finset.mem_filter.mp hjmem).2
  have hjfirst : ∀ i : Fin 4, i < j → k i = 0 := by
    intro i hij
    by_contra hne
    have hiS : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have hjle : j ≤ i := Finset.min'_le s i hiS
    exact (not_lt_of_ge hjle) hij
  rcases lt_or_gt_of_ne hjne with hneg | hpos
  · right
    exact ⟨j, (by intro i hij; simp [hjfirst i hij]), by simpa using neg_pos.mpr hneg⟩
  · left
    exact ⟨j, hjfirst, hpos⟩


theorem fs4CanonicalPairRepresentative_ne_neg (k : FS4Index)
    (hk : fs4CanonicalPairRepresentative k) :
    k ≠ (fun i => -k i) := by
  intro h
  obtain ⟨j, hj0, hjpos⟩ := hk.2
  have heq := congrFun h j
  omega


theorem fs4CanonicalPairRepresentative_neg_not (k : FS4Index)
    (hk : fs4CanonicalPairRepresentative k) :
    ¬ fs4CanonicalPairRepresentative (fun i => -k i) := by
  intro hneg
  obtain ⟨j, hj0, hjpos⟩ := hk.2
  obtain ⟨l, hl0, hlpos⟩ := hneg.2
  by_cases hcompare : j < l
  · have hz : (fun i => -k i) j = 0 := hl0 j hcompare
    have hzk : k j = 0 := by simpa using hz
    omega
  · by_cases hcompare2 : l < j
    · have hz : k l = 0 := hj0 l hcompare2
      have hzn : (fun i => -k i) l = 0 := by simpa using hz
      omega
    · have hEq : j = l := le_antisymm (le_of_not_gt hcompare2)
        (le_of_not_gt hcompare)
      subst l
      have hnegpos : 0 < -k j := by simpa using hlpos
      omega

def fs4GaussianRealPairScale (L mass : ℝ) (k : FS4Index) : ℝ :=
  L^2 / (Real.sqrt 2 * Real.sqrt (torusMassSymbol 4 L mass k))

theorem fs4GaussianRealPairScale_variance (L mass : ℝ) (k : FS4Index)
    (hmass : 0 < mass) :
    2 * (fs4GaussianRealPairScale L mass k)^2 =
      L^4 / torusMassSymbol 4 L mass k := by
  have hpos : 0 < torusMassSymbol 4 L mass k :=
    torusMassSymbol_pos 4 L mass hmass k
  have hroot : Real.sqrt (torusMassSymbol 4 L mass k)^2 =
      torusMassSymbol 4 L mass k :=
    Real.sq_sqrt (le_of_lt hpos)
  have hroot2 : (Real.sqrt 2)^2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [fs4GaussianRealPairScale]
  field_simp [hpos.ne', Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]
  rw [hroot, hroot2]
  ring

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum

def fs4GaussianPairAmplitude (L mass : ℝ) (k : FS4Index) : ℝ :=
  Real.sqrt (fs4SobolevWeight 4 k) * fs4GaussianRealPairScale L mass k

theorem fs4GaussianPairAmplitude_bound (L mass : ℝ) (k : FS4Index) :
    |fs4GaussianPairAmplitude L mass k| ≤
      L^2 * Real.sqrt (fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k) := by
  have hw := fs4SobolevWeight_nonneg 4 k
  have ht : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hn : 0 ≤ fs4GaussianPairAmplitude L mass k := by
    unfold fs4GaussianPairAmplitude fs4GaussianRealPairScale
    positivity
  rw [abs_of_nonneg hn]
  have heq : fs4GaussianPairAmplitude L mass k =
      (L^2 * Real.sqrt (fs4SobolevWeight 4 k / torusMassSymbol 4 L mass k)) /
        Real.sqrt 2 := by
    rw [fs4GaussianPairAmplitude, fs4GaussianRealPairScale, Real.sqrt_div hw]
    ring
  rw [heq]
  exact div_le_self (by positivity) ht

def fs4GaussianRealCosPair (L mass : ℝ) (k : FS4Index) : FS4HminusFourCompletion :=
  fs4RealCosinePairVector k (fs4GaussianPairAmplitude L mass k)

def fs4GaussianRealSinPair (L mass : ℝ) (k : FS4Index) : FS4HminusFourCompletion :=
  fs4RealSinePairVector k (fs4GaussianPairAmplitude L mass k)

theorem fs4GaussianRealCosPair_norm_summable (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun k : FS4Index => ‖fs4GaussianRealCosPair L mass k‖) := by
  apply Summable.of_norm_bounded
    ((fs4_sqrt_weighted_resolvent_summable L mass hL hmass).mul_left (2 * L^2))
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (fs4RealCosinePairVector_norm_le k _).trans (by
    have h := fs4GaussianPairAmplitude_bound L mass k
    change 2 * |fs4GaussianPairAmplitude L mass k| ≤ _
    linarith)

theorem fs4GaussianRealSinPair_norm_summable (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun k : FS4Index => ‖fs4GaussianRealSinPair L mass k‖) := by
  apply Summable.of_norm_bounded
    ((fs4_sqrt_weighted_resolvent_summable L mass hL hmass).mul_left (2 * L^2))
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (fs4RealSinePairVector_norm_le k _).trans (by
    have h := fs4GaussianPairAmplitude_bound L mass k
    change 2 * |fs4GaussianPairAmplitude L mass k| ≤ _
    linarith)

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum

abbrev FS4CanonicalPairIndex := {k : FS4Index // fs4CanonicalPairRepresentative k}

theorem fs4GaussianRealCosPair_mem (L mass : ℝ) (k : FS4CanonicalPairIndex) :
    fs4GaussianRealCosPair L mass k ∈ fs4HminusFourRealCarrier :=
  fs4RealCosinePairVector_mem k _
    (Ne.symm (fs4CanonicalPairRepresentative_ne_neg k k.property))

theorem fs4GaussianRealSinPair_mem (L mass : ℝ) (k : FS4CanonicalPairIndex) :
    fs4GaussianRealSinPair L mass k ∈ fs4HminusFourRealCarrier :=
  fs4RealSinePairVector_mem k _
    (Ne.symm (fs4CanonicalPairRepresentative_ne_neg k k.property))

theorem fs4GaussianCanonicalCosPair_norm_summable
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun k : FS4CanonicalPairIndex => ‖fs4GaussianRealCosPair L mass k‖) :=
  (fs4GaussianRealCosPair_norm_summable L mass hL hmass).subtype _

theorem fs4GaussianCanonicalSinPair_norm_summable
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun k : FS4CanonicalPairIndex => ‖fs4GaussianRealSinPair L mass k‖) :=
  (fs4GaussianRealSinPair_norm_summable L mass hL hmass).subtype _

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

abbrev FS4GaussianSeriesIndex := Unit ⊕ (FS4Index ⊕ FS4Index)

def fs4GaussianSeriesDirection (L mass : ℝ) : FS4GaussianSeriesIndex → FS4HminusFourCompletion := by
  classical
  exact
  fun j => j.elim (fun _ => fs4GaussianZeroDirection L mass)
    (fun s => s.elim
      (fun k => if fs4CanonicalPairRepresentative k then fs4GaussianRealCosPair L mass k else 0)
      (fun k => if fs4CanonicalPairRepresentative k then fs4GaussianRealSinPair L mass k else 0))

def fs4GaussianSeriesEnumeration : ℕ ≃ FS4GaussianSeriesIndex :=
  Classical.choice nonempty_equiv_of_countable

def fs4GaussianNatDirection (L mass : ℝ) (n : ℕ) : FS4HminusFourCompletion :=
  fs4GaussianSeriesDirection L mass (fs4GaussianSeriesEnumeration n)

theorem fs4GaussianSeriesDirection_norm_summable (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun j => ‖fs4GaussianSeriesDirection L mass j‖) := by
  classical
  apply Summable.sum
  · exact Summable.of_finite
  · apply Summable.sum
    · apply Summable.of_norm_bounded (fs4GaussianRealCosPair_norm_summable L mass hL hmass)
      intro k
      simp only [Real.norm_eq_abs, abs_norm]
      by_cases hk : fs4CanonicalPairRepresentative k
      · simp [fs4GaussianSeriesDirection, hk]
      · simp [fs4GaussianSeriesDirection, hk]
    · apply Summable.of_norm_bounded (fs4GaussianRealSinPair_norm_summable L mass hL hmass)
      intro k
      simp only [Real.norm_eq_abs, abs_norm]
      by_cases hk : fs4CanonicalPairRepresentative k
      · simp [fs4GaussianSeriesDirection, hk]
      · simp [fs4GaussianSeriesDirection, hk]

theorem fs4GaussianNatDirection_norm_summable (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Summable (fun n => ‖fs4GaussianNatDirection L mass n‖) :=
  fs4GaussianSeriesEnumeration.summable_iff.mpr
    (fs4GaussianSeriesDirection_norm_summable L mass hL hmass)

def fs4GaussianCarrierRandomElement (L mass : ℝ) : (ℕ → ℝ) → FS4HminusFourCompletion :=
  gaussianHilbertSeriesLimit (fs4GaussianNatDirection L mass)

theorem fs4GaussianCarrierRandomElement_measurable (L mass : ℝ) :
    Measurable (fs4GaussianCarrierRandomElement L mass) :=
  (gaussianHilbertSeriesLimit_stronglyMeasurable _).measurable

theorem fs4GaussianCarrierRandomElement_eq_tsum_ae (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      fs4GaussianCarrierRandomElement L mass ξ = ∑' n, ξ n • fs4GaussianNatDirection L mass n :=
  gaussianHilbertSeriesLimit_eq_tsum_ae _ (fs4GaussianNatDirection_norm_summable L mass hL hmass)

def fs4GaussianCarrierMeasure (L mass : ℝ) : Measure FS4HminusFourCompletion :=
  Measure.map (fs4GaussianCarrierRandomElement L mass) (gaussianNoiseMeasure 1)

instance fs4GaussianCarrierMeasure_isProbability (L mass : ℝ) :
    IsProbabilityMeasure (fs4GaussianCarrierMeasure L mass) := by
  unfold fs4GaussianCarrierMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    (fs4GaussianCarrierRandomElement_measurable L mass).aemeasurable).2 inferInstance

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

theorem fs4RealCarrier_add {x y : FS4HminusFourCompletion}
    (hx : x ∈ fs4HminusFourRealCarrier) (hy : y ∈ fs4HminusFourRealCarrier) :
    x + y ∈ fs4HminusFourRealCarrier := by
  intro k
  change x (fun i => -k i) + y (fun i => -k i) = star (x k + y k)
  rw [hx k, hy k, star_add]

theorem fs4RealCarrier_real_smul (r : ℝ) {x : FS4HminusFourCompletion}
    (hx : x ∈ fs4HminusFourRealCarrier) : r • x ∈ fs4HminusFourRealCarrier := by
  intro k
  change r • x (fun i => -k i) = star (r • x k)
  simp [hx k]

theorem fs4GaussianSeriesDirection_mem (L mass : ℝ) (j : FS4GaussianSeriesIndex) :
    fs4GaussianSeriesDirection L mass j ∈ fs4HminusFourRealCarrier := by
  classical
  rcases j with u | (k | k)
  · intro q
    by_cases hq : q = 0
    · subst q
      have hz : (fun _ : Fin 4 => (0 : ℤ)) = (0 : FS4Index) := rfl
      simp [fs4GaussianSeriesDirection, fs4GaussianZeroDirection, lp.single_apply, Pi.single_apply, hz]
    · have hnq : (fun i => -q i) ≠ 0 := by
        intro h; apply hq
        funext i
        have hi := congrFun h i
        simpa using hi
      simp [fs4GaussianSeriesDirection, fs4GaussianZeroDirection, lp.single_apply, Pi.single_apply, hq, hnq]
  · by_cases hk : fs4CanonicalPairRepresentative k
    · simpa [fs4GaussianSeriesDirection, hk] using fs4GaussianRealCosPair_mem L mass ⟨k, hk⟩
    · simpa [fs4GaussianSeriesDirection, hk] using fs4HminusFour_zero_mem_realCarrier
  · by_cases hk : fs4CanonicalPairRepresentative k
    · simpa [fs4GaussianSeriesDirection, hk] using fs4GaussianRealSinPair_mem L mass ⟨k, hk⟩
    · simpa [fs4GaussianSeriesDirection, hk] using fs4HminusFour_zero_mem_realCarrier

theorem fs4GaussianCarrierRandomElement_mem_ae (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      fs4GaussianCarrierRandomElement L mass ξ ∈ fs4HminusFourRealCarrier := by
  filter_upwards [fs4GaussianCarrierRandomElement_eq_tsum_ae L mass hL hmass,
    gaussianNoiseMeasure_hilbert_series_summable_ae (fs4GaussianNatDirection L mass)
      (fs4GaussianNatDirection_norm_summable L mass hL hmass)] with ξ heq hs
  rw [heq]
  apply fs4HminusFourRealCarrier_closed.mem_of_tendsto hs.hasSum
  apply Filter.Eventually.of_forall
  intro s
  apply Finset.sum_induction
  · intro x y hx hy
    exact fs4RealCarrier_add hx hy
  · exact fs4HminusFour_zero_mem_realCarrier
  · intro n hn
    exact fs4RealCarrier_real_smul _ (fs4GaussianSeriesDirection_mem L mass _)

theorem fs4GaussianCarrierMeasure_realCarrier_ae (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∀ᵐ x ∂fs4GaussianCarrierMeasure L mass, x ∈ fs4HminusFourRealCarrier := by
  unfold fs4GaussianCarrierMeasure
  apply (ae_map_iff (fs4GaussianCarrierRandomElement_measurable L mass).aemeasurable
    (show MeasurableSet {x : FS4HminusFourCompletion | x ∈ fs4HminusFourRealCarrier} from
      fs4HminusFourRealCarrier_closed.measurableSet)).2
  exact fs4GaussianCarrierRandomElement_mem_ae L mass hL hmass

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

def fs4GaussianCosNoiseIndex (k : FS4Index) : ℕ :=
  fs4GaussianSeriesEnumeration.symm (Sum.inr (Sum.inl k))
def fs4GaussianSinNoiseIndex (k : FS4Index) : ℕ :=
  fs4GaussianSeriesEnumeration.symm (Sum.inr (Sum.inr k))

theorem fs4CanonicalPair_not_neg_of_canonical (k q : FS4Index)
    (hk : fs4CanonicalPairRepresentative k) (hq : fs4CanonicalPairRepresentative q) :
    k ≠ (fun i => -q i) := by
  intro heq
  exact fs4CanonicalPairRepresentative_neg_not q hq (heq ▸ hk)

theorem fs4GaussianSeriesDirection_apply_canonical (L mass : ℝ)
    (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) (j : FS4GaussianSeriesIndex) :
    fs4GaussianSeriesDirection L mass j k =
      if j = Sum.inr (Sum.inl k) then (fs4GaussianPairAmplitude L mass k : ℂ)
      else if j = Sum.inr (Sum.inr k) then Complex.I * (fs4GaussianPairAmplitude L mass k : ℂ)
      else 0 := by
  classical
  rcases j with u | (q | q)
  · simp [fs4GaussianSeriesDirection, fs4GaussianZeroDirection, lp.single_apply, hk.1]
  · by_cases hq : fs4CanonicalPairRepresentative q
    · have hn := fs4CanonicalPair_not_neg_of_canonical k q hk hq
      by_cases heq : q = k
      · subst q
        simp [fs4GaussianSeriesDirection, hk, fs4GaussianRealCosPair,
          fs4RealCosinePairVector, fs4RealPairVector, lp.single_apply, hn]
      · simp [fs4GaussianSeriesDirection, hq, fs4GaussianRealCosPair,
          fs4RealCosinePairVector, fs4RealPairVector, lp.single_apply, hn, heq, Ne.symm heq]
    · have heq : q ≠ k := by intro h; exact hq (h.symm ▸ hk)
      simp [fs4GaussianSeriesDirection, hq, heq]
  · by_cases hq : fs4CanonicalPairRepresentative q
    · have hn := fs4CanonicalPair_not_neg_of_canonical k q hk hq
      by_cases heq : q = k
      · subst q
        simp [fs4GaussianSeriesDirection, hk, fs4GaussianRealSinPair,
          fs4RealSinePairVector, fs4RealPairVector, lp.single_apply, hn]
      · simp [fs4GaussianSeriesDirection, hq, fs4GaussianRealSinPair,
          fs4RealSinePairVector, fs4RealPairVector, lp.single_apply, hn, heq, Ne.symm heq]
    · have heq : q ≠ k := by intro h; exact hq (h.symm ▸ hk)
      simp [fs4GaussianSeriesDirection, hq, heq]

theorem fs4GaussianNatDirection_apply_canonical (L mass : ℝ)
    (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) (n : ℕ) :
    fs4GaussianNatDirection L mass n k =
      if n = fs4GaussianCosNoiseIndex k then (fs4GaussianPairAmplitude L mass k : ℂ)
      else if n = fs4GaussianSinNoiseIndex k then Complex.I * (fs4GaussianPairAmplitude L mass k : ℂ)
      else 0 := by
  classical
  rw [fs4GaussianNatDirection, fs4GaussianSeriesDirection_apply_canonical L mass k hk]
  simp only [Equiv.apply_eq_iff_eq_symm_apply, fs4GaussianCosNoiseIndex, fs4GaussianSinNoiseIndex]
  rfl

theorem fs4GaussianCosSinNoiseIndex_ne (k : FS4Index) :
    fs4GaussianCosNoiseIndex k ≠ fs4GaussianSinNoiseIndex k := by
  intro h
  have heq := fs4GaussianSeriesEnumeration.symm.injective h
  cases heq

theorem fs4GaussianCarrierRandomElement_canonical_coordinate_ae (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      fs4GaussianCarrierRandomElement L mass ξ k =
        (ξ (fs4GaussianCosNoiseIndex k) : ℂ) * (fs4GaussianPairAmplitude L mass k : ℂ) +
        (ξ (fs4GaussianSinNoiseIndex k) : ℂ) * (Complex.I * (fs4GaussianPairAmplitude L mass k : ℂ)) := by
  classical
  filter_upwards [fs4GaussianCarrierRandomElement_eq_tsum_ae L mass hL hmass,
    gaussianNoiseMeasure_hilbert_series_summable_ae (fs4GaussianNatDirection L mass)
      (fs4GaussianNatDirection_norm_summable L mass hL hmass)] with ξ heq hs
  rw [heq]
  have hev := (lp.evalCLM ℝ (fun _ : FS4Index => ℂ) 2 k).map_tsum hs
  change (∑' n, ξ n • fs4GaussianNatDirection L mass n) k = _
  change (∑' n, ξ n • fs4GaussianNatDirection L mass n) k =
    ∑' n, (ξ n • fs4GaussianNatDirection L mass n) k at hev
  rw [hev]
  have hz : ∀ n ∉ ({fs4GaussianCosNoiseIndex k, fs4GaussianSinNoiseIndex k} : Finset ℕ),
      (ξ n • fs4GaussianNatDirection L mass n) k = 0 := by
    intro n hn
    have hne : n ≠ fs4GaussianCosNoiseIndex k ∧ n ≠ fs4GaussianSinNoiseIndex k := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
    change ξ n • (fs4GaussianNatDirection L mass n k) = 0
    rw [fs4GaussianNatDirection_apply_canonical L mass k hk]
    simp [hne.1, hne.2]
  rw [tsum_eq_sum hz]
  have hne := fs4GaussianCosSinNoiseIndex_ne k
  simp [Finset.sum_insert, Ne.symm hne, fs4GaussianNatDirection_apply_canonical L mass k hk,
    hne, Complex.real_smul]

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

theorem fs4GaussianCarrierRandomElement_canonical_norm_sq_ae (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      ‖fs4GaussianCarrierRandomElement L mass ξ k‖ ^ 2 =
        (fs4GaussianPairAmplitude L mass k)^2 *
          ((ξ (fs4GaussianCosNoiseIndex k))^2 + (ξ (fs4GaussianSinNoiseIndex k))^2) := by
  filter_upwards [fs4GaussianCarrierRandomElement_canonical_coordinate_ae L mass hL hmass k hk] with ξ heq
  rw [heq, Complex.sq_norm]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

theorem fs4GaussianCarrierRandomElement_canonical_secondMoment (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    (∫ ξ, ‖fs4GaussianCarrierRandomElement L mass ξ k‖ ^ 2 ∂gaussianNoiseMeasure 1) =
      fs4SobolevWeight 4 k * (L^4 / torusMassSymbol 4 L mass k) := by
  rw [integral_congr_ae (fs4GaussianCarrierRandomElement_canonical_norm_sq_ae L mass hL hmass k hk)]
  rw [integral_const_mul, integral_add
    (gaussianNoiseMeasure_coordinate_memLp_two (fs4GaussianCosNoiseIndex k)).integrable_sq
    (gaussianNoiseMeasure_coordinate_memLp_two (fs4GaussianSinNoiseIndex k)).integrable_sq]
  rw [gaussianNoiseMeasure_coordinate_second_moment, gaussianNoiseMeasure_coordinate_second_moment]
  simp only [NNReal.coe_one]
  have hw := Real.sq_sqrt (fs4SobolevWeight_nonneg 4 k)
  have hv := fs4GaussianRealPairScale_variance L mass k hmass
  dsimp [fs4GaussianPairAmplitude]
  rw [mul_pow, hw]
  nlinarith

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

theorem fs4GaussianCarrierMeasure_canonical_secondMoment (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    (∫ x : FS4HminusFourCompletion, ‖x k‖ ^ 2 ∂fs4GaussianCarrierMeasure L mass) =
      fs4SobolevWeight 4 k * (L^4 / torusMassSymbol 4 L mass k) := by
  unfold fs4GaussianCarrierMeasure
  rw [integral_map (fs4GaussianCarrierRandomElement_measurable L mass).aemeasurable
    (show AEStronglyMeasurable (fun x : FS4HminusFourCompletion => ‖x k‖ ^ 2)
      (Measure.map (fs4GaussianCarrierRandomElement L mass) (gaussianNoiseMeasure 1)) from
        ((fs4HminusFour_coordinate_continuous k).norm.pow 2).aestronglyMeasurable)]
  exact fs4GaussianCarrierRandomElement_canonical_secondMoment L mass hL hmass k hk

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

def fs4GaussianZeroNoiseIndex : ℕ :=
  fs4GaussianSeriesEnumeration.symm (Sum.inl ())

theorem fs4GaussianSeriesDirection_apply_zero (L mass : ℝ) (j : FS4GaussianSeriesIndex) :
    fs4GaussianSeriesDirection L mass j 0 =
      if j = Sum.inl () then ((L^2 / mass : ℝ) : ℂ) else 0 := by
  classical
  rcases j with u | (q | q)
  · cases u
    simp [fs4GaussianSeriesDirection, fs4GaussianZeroDirection, lp.single_apply]
  all_goals
    by_cases hq : fs4CanonicalPairRepresentative q
    · have hn : (fun i => -q i) ≠ 0 := by
        intro heq
        apply hq.1
        funext i
        have hi := congrFun heq i
        simpa using hi
      simp [fs4GaussianSeriesDirection, hq, fs4GaussianRealCosPair,
        fs4GaussianRealSinPair, fs4RealCosinePairVector, fs4RealSinePairVector,
        fs4RealPairVector, lp.single_apply, hq.1, Ne.symm hq.1, hn, Ne.symm hn]
    · simp [fs4GaussianSeriesDirection, hq]

theorem fs4GaussianCarrierRandomElement_zero_coordinate_ae (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      fs4GaussianCarrierRandomElement L mass ξ 0 =
        (ξ fs4GaussianZeroNoiseIndex : ℂ) * ((L^2 / mass : ℝ) : ℂ) := by
  classical
  filter_upwards [fs4GaussianCarrierRandomElement_eq_tsum_ae L mass hL hmass,
    gaussianNoiseMeasure_hilbert_series_summable_ae (fs4GaussianNatDirection L mass)
      (fs4GaussianNatDirection_norm_summable L mass hL hmass)] with ξ heq hs
  rw [heq]
  have hev := (lp.evalCLM ℝ (fun _ : FS4Index => ℂ) 2 0).map_tsum hs
  change (∑' n, ξ n • fs4GaussianNatDirection L mass n) 0 = _
  change (∑' n, ξ n • fs4GaussianNatDirection L mass n) 0 =
    ∑' n, (ξ n • fs4GaussianNatDirection L mass n) 0 at hev
  rw [hev]
  have heval (n : ℕ) : (ξ n • fs4GaussianNatDirection L mass n) 0 =
      if n = fs4GaussianZeroNoiseIndex then
        (ξ n : ℂ) * ((L^2 / mass : ℝ) : ℂ) else 0 := by
    change ξ n • (fs4GaussianSeriesDirection L mass (fs4GaussianSeriesEnumeration n) 0) = _
    rw [fs4GaussianSeriesDirection_apply_zero]
    simp only [Equiv.apply_eq_iff_eq_symm_apply, fs4GaussianZeroNoiseIndex]
    split <;> simp_all [Complex.real_smul]
  simp_rw [heval]
  simp

theorem fs4GaussianCarrierRandomElement_negative_coordinate_ae (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      fs4GaussianCarrierRandomElement L mass ξ (fun i => -k i) =
        (ξ (fs4GaussianCosNoiseIndex k) : ℂ) * (fs4GaussianPairAmplitude L mass k : ℂ) -
        (ξ (fs4GaussianSinNoiseIndex k) : ℂ) * (Complex.I * (fs4GaussianPairAmplitude L mass k : ℂ)) := by
  filter_upwards [fs4GaussianCarrierRandomElement_mem_ae L mass hL hmass,
    fs4GaussianCarrierRandomElement_canonical_coordinate_ae L mass hL hmass k hk] with ξ hreal heq
  rw [hreal k, heq]
  simp [sub_eq_add_neg]

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

def fs4GaussianPairVariance (L mass : ℝ) (k : FS4Index) : NNReal :=
  ⟨(fs4GaussianPairAmplitude L mass k)^2, sq_nonneg _⟩

theorem fs4GaussianCarrierRandomElement_canonical_re_ae (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    (fun ξ => (fs4GaussianCarrierRandomElement L mass ξ k).re) =ᵐ[gaussianNoiseMeasure 1]
      (fun ξ => ξ (fs4GaussianCosNoiseIndex k) * fs4GaussianPairAmplitude L mass k) := by
  filter_upwards [fs4GaussianCarrierRandomElement_canonical_coordinate_ae L mass hL hmass k hk] with ξ h
  rw [h]
  simp

theorem fs4GaussianCarrierRandomElement_canonical_im_ae (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    (fun ξ => (fs4GaussianCarrierRandomElement L mass ξ k).im) =ᵐ[gaussianNoiseMeasure 1]
      (fun ξ => ξ (fs4GaussianSinNoiseIndex k) * fs4GaussianPairAmplitude L mass k) := by
  filter_upwards [fs4GaussianCarrierRandomElement_canonical_coordinate_ae L mass hL hmass k hk] with ξ h
  rw [h]
  simp

theorem fs4GaussianCarrierRandomElement_canonical_re_hasLaw (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    HasLaw (fun ξ => (fs4GaussianCarrierRandomElement L mass ξ k).re)
      (gaussianReal 0 (fs4GaussianPairVariance L mass k)) (gaussianNoiseMeasure 1) := by
  have h : HasLaw (fun ξ : ℕ → ℝ => ξ (fs4GaussianCosNoiseIndex k))
      (gaussianReal 0 1) (gaussianNoiseMeasure 1) :=
    ⟨(measurable_pi_apply _).aemeasurable, gaussianNoiseMeasure_coordinate_map 1 _⟩
  have hs := gaussianReal_mul_const h (fs4GaussianPairAmplitude L mass k)
  simp only [mul_zero, mul_one] at hs
  exact hs.congr (fs4GaussianCarrierRandomElement_canonical_re_ae L mass hL hmass k hk)

theorem fs4GaussianCarrierRandomElement_canonical_im_hasLaw (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    HasLaw (fun ξ => (fs4GaussianCarrierRandomElement L mass ξ k).im)
      (gaussianReal 0 (fs4GaussianPairVariance L mass k)) (gaussianNoiseMeasure 1) := by
  have h : HasLaw (fun ξ : ℕ → ℝ => ξ (fs4GaussianSinNoiseIndex k))
      (gaussianReal 0 1) (gaussianNoiseMeasure 1) :=
    ⟨(measurable_pi_apply _).aemeasurable, gaussianNoiseMeasure_coordinate_map 1 _⟩
  have hs := gaussianReal_mul_const h (fs4GaussianPairAmplitude L mass k)
  simp only [mul_zero, mul_one] at hs
  exact hs.congr (fs4GaussianCarrierRandomElement_canonical_im_ae L mass hL hmass k hk)

theorem fs4GaussianCarrierRandomElement_canonical_re_im_indep (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    IndepFun (fun ξ => (fs4GaussianCarrierRandomElement L mass ξ k).re)
      (fun ξ => (fs4GaussianCarrierRandomElement L mass ξ k).im) (gaussianNoiseMeasure 1) := by
  have hind := (gaussianNoiseMeasure_coordinate_independent 1).indepFun (fs4GaussianCosSinNoiseIndex_ne k)
  have hs := hind.comp (show Measurable (fun r : ℝ => r * fs4GaussianPairAmplitude L mass k) by fun_prop)
    (show Measurable (fun r : ℝ => r * fs4GaussianPairAmplitude L mass k) by fun_prop)
  exact hs.congr (fs4GaussianCarrierRandomElement_canonical_re_ae L mass hL hmass k hk).symm
    (fs4GaussianCarrierRandomElement_canonical_im_ae L mass hL hmass k hk).symm

theorem fs4GaussianCarrierMeasure_canonical_pair_law (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4Index) (hk : fs4CanonicalPairRepresentative k) :
    Measure.map (fun x : FS4HminusFourCompletion => ((x k).re, (x k).im))
      (fs4GaussianCarrierMeasure L mass) =
        (gaussianReal 0 (fs4GaussianPairVariance L mass k)).prod
          (gaussianReal 0 (fs4GaussianPairVariance L mass k)) := by
  unfold fs4GaussianCarrierMeasure
  rw [Measure.map_map (show Measurable (fun x : FS4HminusFourCompletion => ((x k).re, (x k).im)) from
      ((Complex.continuous_re.comp (fs4HminusFour_coordinate_continuous k)).prodMk
        (Complex.continuous_im.comp (fs4HminusFour_coordinate_continuous k))).measurable)
    (fs4GaussianCarrierRandomElement_measurable L mass)]
  have hre := fs4GaussianCarrierRandomElement_canonical_re_hasLaw L mass hL hmass k hk
  have him := fs4GaussianCarrierRandomElement_canonical_im_hasLaw L mass hL hmass k hk
  exact (fs4GaussianCarrierRandomElement_canonical_re_im_indep L mass hL hmass k hk).map_prod_eq_prod_map_map
    hre.aemeasurable him.aemeasurable |>.trans (by rw [hre.map_eq, him.map_eq])

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

theorem fs4GaussianPairVariance_normalization (L mass : ℝ) (hmass : 0 < mass) (k : FS4Index) :
    2 * (fs4GaussianPairVariance L mass k : ℝ) =
      fs4SobolevWeight 4 k * (L^4 / torusMassSymbol 4 L mass k) := by
  have hw := Real.sq_sqrt (fs4SobolevWeight_nonneg 4 k)
  have hv := fs4GaussianRealPairScale_variance L mass k hmass
  change 2 * (Real.sqrt (fs4SobolevWeight 4 k) * fs4GaussianRealPairScale L mass k)^2 = _
  rw [mul_pow, hw]
  nlinarith

theorem fs4GaussianCarrierMeasure_zero_re_law (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Measure.map (fun x : FS4HminusFourCompletion => (x 0).re) (fs4GaussianCarrierMeasure L mass) =
      gaussianReal 0 ⟨(L^2 / mass)^2, sq_nonneg _⟩ := by
  unfold fs4GaussianCarrierMeasure
  rw [Measure.map_map (show Measurable (fun x : FS4HminusFourCompletion => (x 0).re) from
      (Complex.continuous_re.comp (fs4HminusFour_coordinate_continuous 0)).measurable)
    (fs4GaussianCarrierRandomElement_measurable L mass)]
  have h : HasLaw (fun ξ : ℕ → ℝ => ξ fs4GaussianZeroNoiseIndex)
      (gaussianReal 0 1) (gaussianNoiseMeasure 1) :=
    ⟨(measurable_pi_apply _).aemeasurable, gaussianNoiseMeasure_coordinate_map 1 _⟩
  have hs := gaussianReal_mul_const h (L^2 / mass)
  simp only [mul_zero, mul_one] at hs
  apply HasLaw.map_eq (hs.congr _)
  filter_upwards [fs4GaussianCarrierRandomElement_zero_coordinate_ae L mass hL hmass] with ξ heq
  change (fs4GaussianCarrierRandomElement L mass ξ 0).re = _
  rw [heq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

abbrev FS4GaussianRealCoordinateIndex := Unit ⊕ (FS4CanonicalPairIndex × Bool)

def fs4GaussianRealCoordinate (j : FS4GaussianRealCoordinateIndex) (x : FS4HminusFourCompletion) : ℝ :=
  j.elim (fun _ => (x 0).re) (fun q => if q.2 then (x q.1).im else (x q.1).re)

def fs4GaussianRealCoordinateScale (L mass : ℝ) (j : FS4GaussianRealCoordinateIndex) : ℝ :=
  j.elim (fun _ => L^2 / mass) (fun q => fs4GaussianPairAmplitude L mass q.1)

def fs4GaussianRealCoordinateNoiseIndex (j : FS4GaussianRealCoordinateIndex) : ℕ :=
  fs4GaussianSeriesEnumeration.symm
    (j.elim (fun _ => Sum.inl ()) (fun q =>
      if q.2 then Sum.inr (Sum.inr q.1.val) else Sum.inr (Sum.inl q.1.val)))

theorem fs4GaussianRealCoordinateNoiseIndex_injective :
    Function.Injective fs4GaussianRealCoordinateNoiseIndex := by
  intro j k h
  have heq := fs4GaussianSeriesEnumeration.symm.injective h
  rcases j with u | ⟨j, b⟩ <;> rcases k with v | ⟨k, c⟩
  · cases u; cases v; rfl
  · cases c <;> simp [fs4GaussianRealCoordinateNoiseIndex] at heq
  · cases b <;> simp [fs4GaussianRealCoordinateNoiseIndex] at heq
  · cases b <;> cases c <;> simp only [Sum.elim_inr, Bool.false_eq_true, ↓reduceIte,
      Sum.inr.injEq, Sum.inl.injEq] at heq
    all_goals simp_all [Subtype.ext_iff]

theorem fs4GaussianRealCoordinate_continuous (j : FS4GaussianRealCoordinateIndex) :
    Continuous (fs4GaussianRealCoordinate j) := by
  rcases j with u | ⟨k, b⟩
  · exact Complex.continuous_re.comp (fs4HminusFour_coordinate_continuous 0)
  · cases b
    · exact Complex.continuous_re.comp (fs4HminusFour_coordinate_continuous k)
    · exact Complex.continuous_im.comp (fs4HminusFour_coordinate_continuous k)

theorem fs4GaussianRealCoordinate_randomElement_ae (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (j : FS4GaussianRealCoordinateIndex) :
    (fun ξ => fs4GaussianRealCoordinate j (fs4GaussianCarrierRandomElement L mass ξ)) =ᵐ[gaussianNoiseMeasure 1]
      (fun ξ => ξ (fs4GaussianRealCoordinateNoiseIndex j) * fs4GaussianRealCoordinateScale L mass j) := by
  rcases j with u | ⟨k, b⟩
  · filter_upwards [fs4GaussianCarrierRandomElement_zero_coordinate_ae L mass hL hmass] with ξ heq
    change (fs4GaussianCarrierRandomElement L mass ξ 0).re = _
    rw [heq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  · cases b
    · exact fs4GaussianCarrierRandomElement_canonical_re_ae L mass hL hmass k k.property
    · exact fs4GaussianCarrierRandomElement_canonical_im_ae L mass hL hmass k k.property

theorem fs4GaussianRealCoordinate_randomElement_hasLaw (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (j : FS4GaussianRealCoordinateIndex) :
    HasLaw (fun ξ => fs4GaussianRealCoordinate j (fs4GaussianCarrierRandomElement L mass ξ))
      (gaussianReal 0 ⟨(fs4GaussianRealCoordinateScale L mass j)^2, sq_nonneg _⟩) (gaussianNoiseMeasure 1) := by
  have h : HasLaw (fun ξ : ℕ → ℝ => ξ (fs4GaussianRealCoordinateNoiseIndex j))
      (gaussianReal 0 1) (gaussianNoiseMeasure 1) :=
    ⟨(measurable_pi_apply _).aemeasurable, gaussianNoiseMeasure_coordinate_map 1 _⟩
  have hs := gaussianReal_mul_const h (fs4GaussianRealCoordinateScale L mass j)
  simp only [mul_zero, mul_one] at hs
  exact hs.congr (fs4GaussianRealCoordinate_randomElement_ae L mass hL hmass j)

theorem fs4GaussianRealCoordinate_randomElement_iIndepFun (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    iIndepFun (fun j ξ => fs4GaussianRealCoordinate j (fs4GaussianCarrierRandomElement L mass ξ))
      (gaussianNoiseMeasure 1) := by
  have h := iIndepFun.precomp fs4GaussianRealCoordinateNoiseIndex_injective
    (gaussianNoiseMeasure_coordinate_independent 1)
  have hs := h.comp (fun j r => r * fs4GaussianRealCoordinateScale L mass j) (by intro j; fun_prop)
  exact hs.congr (fun j => (fs4GaussianRealCoordinate_randomElement_ae L mass hL hmass j).symm)

theorem fs4GaussianCarrierMeasure_finite_realCoordinate_law (m : ℕ) (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hjs : Function.Injective js) :
    Measure.map (fun x : FS4HminusFourCompletion => fun i => fs4GaussianRealCoordinate (js i) x)
      (fs4GaussianCarrierMeasure L mass) =
        Measure.pi (fun i => gaussianReal 0 ⟨(fs4GaussianRealCoordinateScale L mass (js i))^2, sq_nonneg _⟩) := by
  unfold fs4GaussianCarrierMeasure
  rw [Measure.map_map (show Measurable (fun x : FS4HminusFourCompletion => fun i => fs4GaussianRealCoordinate (js i) x) from
    (continuous_pi (fun i => fs4GaussianRealCoordinate_continuous (js i))).measurable)
    (fs4GaussianCarrierRandomElement_measurable L mass)]
  have hind := iIndepFun.precomp hjs (fs4GaussianRealCoordinate_randomElement_iIndepFun L mass hL hmass)
  have hlaw := fun i => fs4GaussianRealCoordinate_randomElement_hasLaw L mass hL hmass (js i)
  simp only [Function.comp_def]
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hlaw i).aemeasurable) hind]
  congr 1
  funext i
  exact (hlaw i).map_eq

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField
open Pphi2Clean.UpstreamLattice

theorem fs4SobolevWeight_pos (s : ℝ) (k : FS4Index) : 0 < fs4SobolevWeight s k := by
  unfold fs4SobolevWeight
  apply Real.rpow_pos_of_pos
  positivity

def fs4PhysicalFourierCoordinate (k : FS4Index) (x : FS4HminusFourCompletion) : ℂ :=
  x k / (Real.sqrt (fs4SobolevWeight 4 k) : ℂ)

theorem fs4PhysicalFourierCoordinate_continuous (k : FS4Index) :
    Continuous (fs4PhysicalFourierCoordinate k) :=
  (fs4HminusFour_coordinate_continuous k).div_const _

theorem fs4PhysicalFourierCoordinate_finiteSource (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N))) (k : FS4Index) :
    fs4PhysicalFourierCoordinate k (fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω) =
      fs4PeriodicComplexFourierLift N a L hperiod ω k := by
  unfold fs4PhysicalFourierCoordinate
  rw [fs4PeriodicFourierFiniteSourceCarrierLiftH4_eq_weightedRaw N a L ha hperiod ω k]
  have hroot : (Real.sqrt (fs4SobolevWeight 4 k) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 4 k)).ne'
  exact mul_div_cancel_left₀ _ hroot

def fs4PhysicalRealCoordinate (j : FS4GaussianRealCoordinateIndex) (x : FS4HminusFourCompletion) : ℝ :=
  j.elim (fun _ => (x 0).re) (fun q =>
    fs4GaussianRealCoordinate j x / Real.sqrt (fs4SobolevWeight 4 q.1))

def fs4PhysicalRealCoordinateScale (L mass : ℝ) (j : FS4GaussianRealCoordinateIndex) : ℝ :=
  j.elim (fun _ => L^2 / mass) (fun q => fs4GaussianRealPairScale L mass q.1)

theorem fs4PhysicalRealCoordinate_continuous (j : FS4GaussianRealCoordinateIndex) :
    Continuous (fs4PhysicalRealCoordinate j) := by
  rcases j with u | ⟨k, b⟩
  · exact Complex.continuous_re.comp (fs4HminusFour_coordinate_continuous 0)
  · exact (fs4GaussianRealCoordinate_continuous (Sum.inr (k,b))).div_const _

theorem fs4PhysicalRealCoordinate_randomElement_ae (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (j : FS4GaussianRealCoordinateIndex) :
    (fun ξ => fs4PhysicalRealCoordinate j (fs4GaussianCarrierRandomElement L mass ξ)) =ᵐ[gaussianNoiseMeasure 1]
      (fun ξ => ξ (fs4GaussianRealCoordinateNoiseIndex j) * fs4PhysicalRealCoordinateScale L mass j) := by
  filter_upwards [fs4GaussianRealCoordinate_randomElement_ae L mass hL hmass j] with ξ heq
  rcases j with u | ⟨k,b⟩
  · exact heq
  · change fs4GaussianRealCoordinate (Sum.inr (k,b)) (fs4GaussianCarrierRandomElement L mass ξ) /
      Real.sqrt (fs4SobolevWeight 4 k) = _
    rw [heq]
    change ξ (fs4GaussianRealCoordinateNoiseIndex (Sum.inr (k,b))) *
      (Real.sqrt (fs4SobolevWeight 4 k) * fs4GaussianRealPairScale L mass k) /
      Real.sqrt (fs4SobolevWeight 4 k) = _
    have hroot := (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 4 k)).ne'
    field_simp
    rfl

theorem fs4PhysicalRealCoordinate_randomElement_hasLaw (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (j : FS4GaussianRealCoordinateIndex) :
    HasLaw (fun ξ => fs4PhysicalRealCoordinate j (fs4GaussianCarrierRandomElement L mass ξ))
      (gaussianReal 0 ⟨(fs4PhysicalRealCoordinateScale L mass j)^2, sq_nonneg _⟩) (gaussianNoiseMeasure 1) := by
  have h : HasLaw (fun ξ : ℕ → ℝ => ξ (fs4GaussianRealCoordinateNoiseIndex j))
      (gaussianReal 0 1) (gaussianNoiseMeasure 1) :=
    ⟨(measurable_pi_apply _).aemeasurable, gaussianNoiseMeasure_coordinate_map 1 _⟩
  have hs := gaussianReal_mul_const h (fs4PhysicalRealCoordinateScale L mass j)
  simp only [mul_zero, mul_one] at hs
  exact hs.congr (fs4PhysicalRealCoordinate_randomElement_ae L mass hL hmass j)

theorem fs4PhysicalRealCoordinate_randomElement_iIndepFun (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    iIndepFun (fun j ξ => fs4PhysicalRealCoordinate j (fs4GaussianCarrierRandomElement L mass ξ))
      (gaussianNoiseMeasure 1) := by
  have h := iIndepFun.precomp fs4GaussianRealCoordinateNoiseIndex_injective
    (gaussianNoiseMeasure_coordinate_independent 1)
  have hs := h.comp (fun j r => r * fs4PhysicalRealCoordinateScale L mass j) (by intro j; fun_prop)
  exact hs.congr (fun j => (fs4PhysicalRealCoordinate_randomElement_ae L mass hL hmass j).symm)

theorem fs4GaussianCarrierMeasure_finite_physicalRealCoordinate_law (m : ℕ) (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hjs : Function.Injective js) :
    Measure.map (fun x : FS4HminusFourCompletion => fun i => fs4PhysicalRealCoordinate (js i) x)
      (fs4GaussianCarrierMeasure L mass) =
        Measure.pi (fun i => gaussianReal 0 ⟨(fs4PhysicalRealCoordinateScale L mass (js i))^2, sq_nonneg _⟩) := by
  unfold fs4GaussianCarrierMeasure
  rw [Measure.map_map (show Measurable (fun x : FS4HminusFourCompletion => fun i => fs4PhysicalRealCoordinate (js i) x) from
    (continuous_pi (fun i => fs4PhysicalRealCoordinate_continuous (js i))).measurable)
    (fs4GaussianCarrierRandomElement_measurable L mass)]
  have hind := iIndepFun.precomp hjs (fs4PhysicalRealCoordinate_randomElement_iIndepFun L mass hL hmass)
  have hlaw := fun i => fs4PhysicalRealCoordinate_randomElement_hasLaw L mass hL hmass (js i)
  simp only [Function.comp_def]
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hlaw i).aemeasurable) hind]
  congr 1
  funext i
  exact (hlaw i).map_eq

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField Pphi2Clean.UpstreamLattice

theorem fs4PhysicalRealCoordinate_finiteSource_canonical (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (k : FS4CanonicalPairIndex) (useSine : Bool) :
    fs4PhysicalRealCoordinate (Sum.inr (k,useSine))
      (fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω) =
      if useSine then
        (latticeEmbedLift (physicalTestEval 4 N a) ω) (periodicSineTest 4 L k hperiod)
      else (latticeEmbedLift (physicalTestEval 4 N a) ω) (periodicCosineTest 4 L k hperiod) := by
  have hroot := (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 4 k)).ne'
  cases useSine <;> dsimp [fs4PhysicalRealCoordinate, fs4GaussianRealCoordinate]
  all_goals rw [fs4PeriodicFourierFiniteSourceCarrierLiftH4_eq_weightedRaw N a L ha hperiod ω k]
  all_goals simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero, fs4PeriodicComplexFourierLift_apply, fs4PeriodicComplexFourierProbe,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  all_goals exact mul_div_cancel_left₀ _ hroot

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField Pphi2Clean.UpstreamLattice

def fs4PhysicalCoordinateTest (L : ℝ) (hL : 0 < L) (j : FS4GaussianRealCoordinateIndex) :
    BoundedContinuousFunction (Fin 4 → ℝ) ℝ :=
  j.elim (fun _ => periodicCosineTest 4 L 0 hL) (fun q =>
    if q.2 then periodicSineTest 4 L q.1 hL else periodicCosineTest 4 L q.1 hL)

theorem fs4PhysicalCoordinateTest_periodic (L : ℝ) (hL : 0 < L) (j : FS4GaussianRealCoordinateIndex) :
    IsFlatTorusPeriodic 4 L (fs4PhysicalCoordinateTest L hL j) := by
  rcases j with u | ⟨k,b⟩
  · exact periodicCosineTest_isFlatTorusPeriodic 4 L hL 0
  · cases b
    · exact periodicCosineTest_isFlatTorusPeriodic 4 L hL k
    · exact periodicSineTest_isFlatTorusPeriodic 4 L hL k

theorem fs4PhysicalCoordinateTest_diagonal (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (j : FS4GaussianRealCoordinateIndex) :
    (torusFourierGreenPairing 4 L mass (fs4PhysicalCoordinateTest L hL j)
      (fs4PhysicalCoordinateTest L hL j)).re = (fs4PhysicalRealCoordinateScale L mass j)^2 := by
  have hzcast : (((L : ℂ)^4 / (mass : ℂ)^2).re) = L^4 / mass^2 := by norm_cast
  rcases j with u | ⟨k,b⟩
  · change (torusFourierGreenPairing 4 L mass (periodicCosineTest 4 L 0 hL)
      (periodicCosineTest 4 L 0 hL)).re = (L^2 / mass)^2
    rw [fs4PeriodicResolvent_zeroCosine_pairing L mass hL hmass, hzcast]
    ring
  · have hk : ∃ i, (k : FS4Index) i ≠ 0 := by
      simpa only [Pi.zero_apply] using Function.ne_iff.mp k.property.1
    have hc : ((((L : ℂ)^4 / (torusMassSymbol 4 L mass k : ℂ))/2).re) =
        (L^4 / torusMassSymbol 4 L mass k)/2 := by norm_cast
    have hv := fs4GaussianRealPairScale_variance L mass k hmass
    cases b
    · change (torusFourierGreenPairing 4 L mass (periodicCosineTest 4 L k hL)
        (periodicCosineTest 4 L k hL)).re = (fs4GaussianRealPairScale L mass k)^2
      rw [fs4_nonzero_cosine_pairing_test L mass hL hmass k hk, hc]
      linarith
    · change (torusFourierGreenPairing 4 L mass (periodicSineTest 4 L k hL)
        (periodicSineTest 4 L k hL)).re = (fs4GaussianRealPairScale L mass k)^2
      rw [fs4_nonzero_sine_pairing_test L mass hL hmass k hk, hc]
      linarith

theorem fs4PhysicalCoordinateTest_zero_cross (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k : FS4CanonicalPairIndex) (b : Bool) :
    (torusFourierGreenPairing 4 L mass (fs4PhysicalCoordinateTest L hL (Sum.inl ()))
      (fs4PhysicalCoordinateTest L hL (Sum.inr (k,b)))).re = 0 := by
  have hk : (0 : FS4Index) ≠ k := Ne.symm k.property.1
  have hn : (0 : FS4Index) ≠ -(k : FS4Index) := by
    intro h
    apply k.property.1
    funext i
    have hi := congrFun h i
    simpa using hi.symm
  cases b
  · exact fs4_cosine_cross_disjoint_test L mass hL hmass 0 k hk hn
  · exact fs4_cosine_sine_cross_test L mass hL hmass 0 k

theorem fs4PhysicalCoordinateTest_cross (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (j q : FS4GaussianRealCoordinateIndex) (hjq : j ≠ q) :
    (torusFourierGreenPairing 4 L mass (fs4PhysicalCoordinateTest L hL j)
      (fs4PhysicalCoordinateTest L hL q)).re = 0 := by
  rcases j with u | ⟨k,b⟩ <;> rcases q with v | ⟨l,c⟩
  · cases u; cases v; exact (hjq rfl).elim
  · cases u
    exact fs4PhysicalCoordinateTest_zero_cross L mass hL hmass l c
  · cases v
    rw [torusFourierGreenPairing_symm]
    exact fs4PhysicalCoordinateTest_zero_cross L mass hL hmass k b
  · have hn : (k : FS4Index) ≠ -(l : FS4Index) :=
      fs4CanonicalPair_not_neg_of_canonical k l k.property l.property
    cases b <;> cases c
    · have hkl : (k : FS4Index) ≠ l := by
        intro h
        apply hjq
        congr 2
        exact Subtype.ext h
      exact fs4_cosine_cross_disjoint_test L mass hL hmass k l hkl hn
    · exact fs4_cosine_sine_cross_test L mass hL hmass k l
    · rw [torusFourierGreenPairing_symm]
      exact fs4_cosine_sine_cross_test L mass hL hmass l k
    · have hkl : (k : FS4Index) ≠ l := by
        intro h
        apply hjq
        congr 2
        exact Subtype.ext h
      exact fs4_sine_cross_disjoint_test L mass hL hmass k l hkl hn

theorem fs4PhysicalCoordinateTest_covariance (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (j q : FS4GaussianRealCoordinateIndex) :
    (torusFourierGreenPairing 4 L mass (fs4PhysicalCoordinateTest L hL j)
      (fs4PhysicalCoordinateTest L hL q)).re =
        if j = q then (fs4PhysicalRealCoordinateScale L mass j)^2 else 0 := by
  classical
  by_cases h : j = q
  · subst q
    simp only [ite_true]
    exact fs4PhysicalCoordinateTest_diagonal L mass hL hmass j
  · rw [if_neg h]
    exact fs4PhysicalCoordinateTest_cross L mass hL hmass j q h

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

theorem fs4PhysicalCoordinateTest_resolventCovarianceMatrix (m : ℕ) (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hjs : Function.Injective js) (i j : Fin m) :
    periodicResolventCovarianceMatrix 4 m L mass hmass (fun i => fs4PhysicalCoordinateTest L hL (js i)) i j =
      if i = j then (fs4PhysicalRealCoordinateScale L mass (js i))^2 else 0 := by
  classical
  unfold periodicResolventCovarianceMatrix
  rw [← torusFourierGreenPairing_eq_physicalTorusResolventPairing 4 L mass hL hmass]
  rw [fs4PhysicalCoordinateTest_covariance L mass hL hmass]
  simp only [hjs.eq_iff]

theorem fs4PhysicalCoordinateTest_fixedVolume_covariance_tendsto (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (j q : FS4GaussianRealCoordinateIndex) :
    Filter.Tendsto
      (fixedVolumeCovarianceInner 4 L mass hL hmass
        (fs4PhysicalCoordinateTest L hL j) (fs4PhysicalCoordinateTest L hL q))
      Filter.atTop (nhds (if j = q then (fs4PhysicalRealCoordinateScale L mass j)^2 else 0)) := by
  have h := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 4 L mass hL hmass
    (fs4PhysicalCoordinateTest L hL j) (fs4PhysicalCoordinateTest L hL q)
    (fs4PhysicalCoordinateTest_periodic L hL j) (fs4PhysicalCoordinateTest_periodic L hL q)
  rwa [fs4PhysicalCoordinateTest_covariance L mass hL hmass] at h

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField

def fs4PhysicalFiniteProjection {m : ℕ} (js : Fin m → FS4GaussianRealCoordinateIndex)
    (x : FS4HminusFourCompletion) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => fs4PhysicalRealCoordinate (js i) x)

theorem fs4PhysicalFiniteProjection_continuous {m : ℕ} (js : Fin m → FS4GaussianRealCoordinateIndex) :
    Continuous (fs4PhysicalFiniteProjection js) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.continuous.comp
    (continuous_pi (fun i => fs4PhysicalRealCoordinate_continuous (js i)))

def fs4PhysicalFiniteMarginal {m : ℕ} (L mass : ℝ) (js : Fin m → FS4GaussianRealCoordinateIndex) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  Measure.map (fs4PhysicalFiniteProjection js) (fs4GaussianCarrierMeasure L mass)

instance fs4PhysicalFiniteMarginal_probability {m : ℕ} (L mass : ℝ) (js : Fin m → FS4GaussianRealCoordinateIndex) :
    IsProbabilityMeasure (fs4PhysicalFiniteMarginal L mass js) := by
  unfold fs4PhysicalFiniteMarginal
  exact (Measure.isProbabilityMeasure_map_iff
    (fs4PhysicalFiniteProjection_continuous js).measurable.aemeasurable).2 inferInstance

theorem fs4PhysicalFiniteMarginal_eq_noiseMap {m : ℕ} (L mass : ℝ) (js : Fin m → FS4GaussianRealCoordinateIndex) :
    fs4PhysicalFiniteMarginal L mass js =
      Measure.map (fun ξ => fs4PhysicalFiniteProjection js (fs4GaussianCarrierRandomElement L mass ξ))
        (gaussianNoiseMeasure 1) := by
  unfold fs4PhysicalFiniteMarginal fs4GaussianCarrierMeasure
  rw [Measure.map_map (fs4PhysicalFiniteProjection_continuous js).measurable
    (fs4GaussianCarrierRandomElement_measurable L mass)]
  rfl

theorem fs4PhysicalFiniteMarginal_hasGaussianLaw {m : ℕ} (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hjs : Function.Injective js) : HasGaussianLaw id (fs4PhysicalFiniteMarginal L mass js) := by
  have hind := iIndepFun.precomp hjs (fs4PhysicalRealCoordinate_randomElement_iIndepFun L mass hL hmass)
  have hG := iIndepFun.hasGaussianLaw
    (by
      intro i
      have h := fs4PhysicalRealCoordinate_randomElement_hasLaw L mass hL hmass (js i)
      refine ⟨h.aemeasurable, ?_⟩
      rw [h.map_eq]
      exact isGaussian_gaussianReal _ _) hind
  have hv := hG.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap
  have hvec : HasGaussianLaw (fun ξ => fs4PhysicalFiniteProjection js (fs4GaussianCarrierRandomElement L mass ξ))
      (gaussianNoiseMeasure 1) := by exact hv
  rw [fs4PhysicalFiniteMarginal_eq_noiseMap]
  exact hvec.isGaussian_map.hasGaussianLaw_id

theorem fs4PhysicalFiniteProjection_inner_ae {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (t : EuclideanSpace ℝ (Fin m)) :
    (fun ξ => inner ℝ t (fs4PhysicalFiniteProjection js (fs4GaussianCarrierRandomElement L mass ξ))) =ᵐ[gaussianNoiseMeasure 1]
      (fun ξ => ∑ i : Fin m, (t i * fs4PhysicalRealCoordinateScale L mass (js i)) *
        ξ (fs4GaussianRealCoordinateNoiseIndex (js i))) := by
  have h := ae_all_iff.2 (fun i => fs4PhysicalRealCoordinate_randomElement_ae L mass hL hmass (js i))
  filter_upwards [h] with ξ hξ
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change fs4PhysicalRealCoordinate (js i) (fs4GaussianCarrierRandomElement L mass ξ) * t i = _
  rw [hξ i]
  ring

theorem fs4PhysicalFiniteMarginal_mean {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (t : EuclideanSpace ℝ (Fin m)) :
    ∫ z, inner ℝ t z ∂fs4PhysicalFiniteMarginal L mass js = 0 := by
  rw [fs4PhysicalFiniteMarginal_eq_noiseMap, integral_map
    (show AEMeasurable (fun ξ => fs4PhysicalFiniteProjection js (fs4GaussianCarrierRandomElement L mass ξ))
      (gaussianNoiseMeasure 1) from ((fs4PhysicalFiniteProjection_continuous js).measurable.comp
        (fs4GaussianCarrierRandomElement_measurable L mass)).aemeasurable) (by fun_prop)]
  rw [integral_congr_ae (fs4PhysicalFiniteProjection_inner_ae L mass hL hmass js t)]
  rw [integral_finsetSum]
  · simp only [integral_const_mul, gaussianNoiseMeasure_coordinate_integral_zero, mul_zero, Finset.sum_const_zero]
  · intro i hi
    exact ((gaussianNoiseMeasure_coordinate_memLp_two _).integrable (by norm_num)).const_mul _

theorem fs4PhysicalFiniteMarginal_variance {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (hjs : Function.Injective js)
    (t : EuclideanSpace ℝ (Fin m)) :
    Var[fun z => inner ℝ t z; fs4PhysicalFiniteMarginal L mass js] =
      ∑ i : Fin m, (t i * fs4PhysicalRealCoordinateScale L mass (js i))^2 := by
  rw [fs4PhysicalFiniteMarginal_eq_noiseMap, variance_map (by fun_prop)
    (show AEMeasurable (fun ξ => fs4PhysicalFiniteProjection js (fs4GaussianCarrierRandomElement L mass ξ))
      (gaussianNoiseMeasure 1) from ((fs4PhysicalFiniteProjection_continuous js).measurable.comp
        (fs4GaussianCarrierRandomElement_measurable L mass)).aemeasurable)]
  simp only [Function.comp_def]
  rw [variance_congr (fs4PhysicalFiniteProjection_inner_ae L mass hL hmass js t)]
  let X : Fin m → (ℕ → ℝ) → ℝ := fun i ξ =>
    (t i * fs4PhysicalRealCoordinateScale L mass (js i)) * ξ (fs4GaussianRealCoordinateNoiseIndex (js i))
  have hind := iIndepFun.precomp (fs4GaussianRealCoordinateNoiseIndex_injective.comp hjs)
    (gaussianNoiseMeasure_coordinate_independent 1)
  have hX : iIndepFun X (gaussianNoiseMeasure 1) :=
    hind.comp (fun i r => (t i * fs4PhysicalRealCoordinateScale L mass (js i)) * r) (by intro i; fun_prop)
  have hm : ∀ i, MemLp (X i) 2 (gaussianNoiseMeasure 1) := fun i =>
    (gaussianNoiseMeasure_coordinate_memLp_two _).const_mul _
  have heq : (fun ξ => ∑ i : Fin m, X i ξ) = ∑ i : Fin m, X i := by
    funext ξ
    simp only [Finset.sum_apply]
  change Var[fun ξ => ∑ i : Fin m, X i ξ; gaussianNoiseMeasure 1] = _
  rw [heq, IndepFun.variance_sum (fun i _ => hm i) (fun i _ j _ hij => hX.indepFun hij)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [X, variance_const_mul, gaussianNoiseMeasure_coordinate_variance, mul_one]

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

theorem fs4PhysicalFiniteMarginal_eq_resolventTarget {m : ℕ} (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hjs : Function.Injective js) :
    fs4PhysicalFiniteMarginal L mass js = periodicResolventTargetMeasure 4 m L mass hmass
      (fun i => fs4PhysicalCoordinateTest L hL (js i)) := by
  have hv (t : EuclideanSpace ℝ (Fin m)) :
      (∑ i : Fin m, ∑ j : Fin m, t i * t j * periodicResolventCovarianceMatrix 4 m L mass hmass
        (fun i => fs4PhysicalCoordinateTest L hL (js i)) i j) =
          ∑ i : Fin m, (t i * fs4PhysicalRealCoordinateScale L mass (js i))^2 := by
    classical
    trans ∑ i : Fin m, t i * t i * (fs4PhysicalRealCoordinateScale L mass (js i))^2
    · apply Finset.sum_congr rfl
      intro i hi
      simp_rw [fs4PhysicalCoordinateTest_resolventCovarianceMatrix m L mass hL hmass js hjs]
      simp
    · apply Finset.sum_congr rfl
      intro i hi
      ring
  letI : IsProbabilityMeasure (periodicResolventTargetMeasure 4 m L mass hmass
      (fun i => fs4PhysicalCoordinateTest L hL (js i))) := by
    unfold periodicResolventTargetMeasure
    infer_instance
  apply Measure.ext_of_charFun
  funext t
  have hleft := (fs4PhysicalFiniteMarginal_hasGaussianLaw L mass hL hmass js hjs).charFun_map_eq t
  have hright := (periodicResolventTargetMeasure_hasGaussianLaw 4 m L mass hmass
    (fun i => fs4PhysicalCoordinateTest L hL (js i))).charFun_map_eq t
  simp only [Measure.map_id, id_eq] at hleft hright
  rw [hleft, hright, fs4PhysicalFiniteMarginal_mean L mass hL hmass js t,
    periodicResolventTargetMeasure_mean_zero 4 m L mass hmass,
    fs4PhysicalFiniteMarginal_variance L mass hL hmass js hjs t,
    periodicResolventTargetMeasure_covariance_quadratic 4 m L mass hL hmass, hv t]

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.GaussianField Pphi2Clean.UpstreamLattice

theorem fs4SobolevWeight_zero (s : ℝ) : fs4SobolevWeight s 0 = 1 := by
  have hz : fs4SplitIndex (0 : FS4Index) = (0,0) := rfl
  simp [fs4SobolevWeight, hz]

theorem fs4PhysicalRealCoordinate_finiteSource (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hperiod : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 4 N)))
    (j : FS4GaussianRealCoordinateIndex) :
    fs4PhysicalRealCoordinate j (fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω) =
      (latticeEmbedLift (physicalTestEval 4 N a) ω) (fs4PhysicalCoordinateTest L hperiod j) := by
  rcases j with u | ⟨k,b⟩
  · change (fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hperiod ω 0).re = _
    rw [fs4PeriodicFourierFiniteSourceCarrierLiftH4_eq_weightedRaw N a L ha hperiod ω 0]
    simp only [fs4SobolevWeight_zero, Real.sqrt_one, Complex.ofReal_one, one_mul]
    simp [fs4PeriodicComplexFourierLift_apply, fs4PeriodicComplexFourierProbe, fs4PhysicalCoordinateTest]
  · simpa only [fs4PhysicalCoordinateTest, Sum.elim_inr, apply_ite] using
      fs4PhysicalRealCoordinate_finiteSource_canonical N a L ha hperiod ω k b

theorem fs4PhysicalFiniteProjection_latticeMeasure_eq_family (N m : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hNa : a * (N:ℝ) = L) (hL : 0 < L)
    (js : Fin m → FS4GaussianRealCoordinateIndex) :
    Measure.map (fs4PhysicalFiniteProjection js)
      (fs4PeriodicFourierFiniteSourceHminusFourMeasure N a mass L ha hmass hNa hL) =
        physicalFamilyEvalMeasure 4 N m a mass ha hmass (fun i => fs4PhysicalCoordinateTest L hL (js i)) := by
  unfold fs4PeriodicFourierFiniteSourceHminusFourMeasure physicalFamilyEvalMeasure physicalGJMeasure
  rw [Measure.map_map (fs4PhysicalFiniteProjection_continuous js).measurable
    (measurable_fs4PeriodicFourierFiniteSourceCarrierLiftH4 N a L hL)]
  have hmeas : Measurable (physicalFamilyEvalMap 4 N m a mass ha hmass
      (fun i => fs4PhysicalCoordinateTest L hL (js i))) := by
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.continuous.measurable.comp
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply _).comp (comap_measurable _)))
  rw [Measure.map_map hmeas (latticeEmbedLift_measurable (physicalTestEval 4 N a))]
  congr 1
  funext ω
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).injective
  funext i
  exact fs4PhysicalRealCoordinate_finiteSource N a L ha hL ω (js i)

def fs4PhysicalCoordinateMode (j : FS4GaussianRealCoordinateIndex) : FS4Index :=
  j.elim (fun _ => 0) (fun q => q.1)

def fs4PhysicalCoordinateUseSine (j : FS4GaussianRealCoordinateIndex) : Bool :=
  j.elim (fun _ => false) (fun q => q.2)

theorem fs4PhysicalCoordinateTest_eq_family (m : ℕ) (L : ℝ) (hL : 0 < L)
    (js : Fin m → FS4GaussianRealCoordinateIndex) :
    (fun i => fs4PhysicalCoordinateTest L hL (js i)) =
      periodicFourierTestFamily 4 m L hL (fun i => fs4PhysicalCoordinateMode (js i))
        (fun i => fs4PhysicalCoordinateUseSine (js i)) := by
  have hpoint (j : FS4GaussianRealCoordinateIndex) :
      fs4PhysicalCoordinateTest L hL j =
        (if fs4PhysicalCoordinateUseSine j then
          periodicSineTest 4 L (fs4PhysicalCoordinateMode j) hL
         else periodicCosineTest 4 L (fs4PhysicalCoordinateMode j) hL) := by
    rcases j with u | ⟨k,b⟩
    · rfl
    · rfl
  exact funext (fun i => hpoint (js i))

def fs4GaussianCarrierProbabilityMeasure (L mass : ℝ) : ProbabilityMeasure FS4HminusFourCompletion :=
  ⟨fs4GaussianCarrierMeasure L mass, inferInstance⟩

theorem fs4PeriodicFixedVolume_finitePhysicalMarginal_tendsto (m : ℕ) (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (js : Fin m → FS4GaussianRealCoordinateIndex)
    (hjs : Function.Injective js) :
    Filter.Tendsto
      (fun n => (fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass n).map
        (fs4PhysicalFiniteProjection js)) Filter.atTop
      (nhds ((fs4GaussianCarrierProbabilityMeasure L mass).map (fs4PhysicalFiniteProjection js))) := by
  have h := fs4PeriodicFourierTestFamily_fixedVolume_weak_tendsto m L mass hL hmass
    (fun i => fs4PhysicalCoordinateMode (js i)) (fun i => fs4PhysicalCoordinateUseSine (js i))
  rw [← fs4PhysicalCoordinateTest_eq_family m L hL js] at h
  have hseq (n : ℕ) : (fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass n).map
        (fs4PhysicalFiniteProjection js) =
      (let N := n+1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure 4 N m (L/(N:ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
          (fun i => fs4PhysicalCoordinateTest L hL (js i))) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    · exact fs4PhysicalFiniteProjection_latticeMeasure_eq_family _ m _ mass L _ hmass (by field_simp) hL js
  have ht : (fs4GaussianCarrierProbabilityMeasure L mass).map (fs4PhysicalFiniteProjection js) =
      periodicResolventTargetProbabilityMeasure 4 m L mass hmass
        (fun i => fs4PhysicalCoordinateTest L hL (js i)) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    · exact fs4PhysicalFiniteMarginal_eq_resolventTarget L mass hL hmass js hjs
  rw [ht]
  exact h.congr' (Filter.Eventually.of_forall (fun n => (hseq n).symm))

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

theorem fs4Periodic_subsequence_limit_finitePhysicalMarginal (m : ℕ) (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (ν : ProbabilityMeasure FS4HminusFourCompletion)
    (hν : Tendsto (fun n => fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass (ns n)) atTop (𝓝 ν))
    (js : Fin m → FS4GaussianRealCoordinateIndex) (hjs : Function.Injective js) :
    ν.map (fs4PhysicalFiniteProjection js) =
      (fs4GaussianCarrierProbabilityMeasure L mass).map (fs4PhysicalFiniteProjection js) := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ ν hν
    (fs4PhysicalFiniteProjection_continuous js)
  have htarget := (fs4PeriodicFixedVolume_finitePhysicalMarginal_tendsto m L mass hL hmass js hjs).comp hns
  exact tendsto_nhds_unique hmap htarget

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

theorem fs4PeriodicFixedVolume_realCarrier_ae (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    ∀ᵐ x ∂(fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass n : Measure FS4HminusFourCompletion),
      x ∈ fs4HminusFourRealCarrier := by
  change ∀ᵐ x ∂Measure.map (fs4PeriodicFourierFiniteSourceCarrierLiftH4 (n+1) (L/((n+1:ℕ):ℝ)) L hL) _,
    x ∈ fs4HminusFourRealCarrier
  apply (ae_map_iff (measurable_fs4PeriodicFourierFiniteSourceCarrierLiftH4 _ _ _ _).aemeasurable
    fs4HminusFourRealCarrier_closed.measurableSet).2
  exact Filter.Eventually.of_forall (fun ω => fs4PeriodicFourierFiniteSourceCarrierLiftH4_mem_realCarrier
    _ _ L (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hL ω)

theorem fs4HminusFour_realCarrier_ae_of_weak_tendsto (μs : ℕ → ProbabilityMeasure FS4HminusFourCompletion)
    (ν : ProbabilityMeasure FS4HminusFourCompletion) (hν : Tendsto μs atTop (𝓝 ν))
    (hs : ∀ n, ∀ᵐ x ∂(μs n : Measure FS4HminusFourCompletion), x ∈ fs4HminusFourRealCarrier) :
    ∀ᵐ x ∂(ν : Measure FS4HminusFourCompletion), x ∈ fs4HminusFourRealCarrier := by
  letI : TopologicalSpace.SeparableSpace FS4HminusFourCompletion := fs4HminusFourCompletion_separable
  have hzero (n : ℕ) : (μs n : Measure FS4HminusFourCompletion) fs4HminusFourRealCarrierᶜ = 0 :=
    ae_iff.mp (hs n)
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν fs4HminusFourRealCarrier_closed.isOpen_compl
  have hle0 : (ν : Measure FS4HminusFourCompletion) fs4HminusFourRealCarrierᶜ ≤ 0 := by
    simpa only [hzero, liminf_const] using hle
  exact ae_iff.mpr (le_antisymm hle0 bot_le)

theorem fs4Periodic_subsequence_limit_realCarrier_ae (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (ν : ProbabilityMeasure FS4HminusFourCompletion)
    (hν : Tendsto (fun n => fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass (ns n)) atTop (𝓝 ν)) :
    ∀ᵐ x ∂(ν : Measure FS4HminusFourCompletion), x ∈ fs4HminusFourRealCarrier :=
  fs4HminusFour_realCarrier_ae_of_weak_tendsto _ ν hν
    (fun n => fs4PeriodicFixedVolume_realCarrier_ae L mass hL hmass (ns n))

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

def fs4PhysicalCoordinateEncoding (x : FS4HminusFourCompletion) : FS4GaussianRealCoordinateIndex → ℝ :=
  fun j => fs4PhysicalRealCoordinate j x

theorem fs4PhysicalCoordinateEncoding_continuous : Continuous fs4PhysicalCoordinateEncoding :=
  continuous_pi (fun j => fs4PhysicalRealCoordinate_continuous j)

theorem fs4PhysicalCoordinateEncoding_injOn :
    Set.InjOn fs4PhysicalCoordinateEncoding fs4HminusFourRealCarrier := by
  intro x hx y hy heq
  have h (j : FS4GaussianRealCoordinateIndex) := congrFun heq j
  have hcanonical (k : FS4CanonicalPairIndex) : x k = y k := by
    have hr := h (Sum.inr (k,false))
    have hi := h (Sum.inr (k,true))
    change (x k).re / Real.sqrt (fs4SobolevWeight 4 k) =
      (y k).re / Real.sqrt (fs4SobolevWeight 4 k) at hr
    change (x k).im / Real.sqrt (fs4SobolevWeight 4 k) =
      (y k).im / Real.sqrt (fs4SobolevWeight 4 k) at hi
    have hroot := (Real.sqrt_pos.mpr (fs4SobolevWeight_pos 4 k)).ne'
    exact Complex.ext ((div_left_inj' hroot).mp hr) ((div_left_inj' hroot).mp hi)
  have hz : x 0 = y 0 := by
    have hr := h (Sum.inl ())
    change (x 0).re = (y 0).re at hr
    have hxi := congrArg Complex.im (hx 0)
    have hyi := congrArg Complex.im (hy 0)
    change (x 0).im = -(x 0).im at hxi
    change (y 0).im = -(y 0).im at hyi
    apply Complex.ext hr
    linarith
  apply lp.ext
  funext k
  by_cases hk : k = 0
  · simpa [hk] using hz
  · rcases fs4FirstNonzeroPositive_or_neg k hk with hpos | hneg
    · exact hcanonical ⟨k,hk,hpos⟩
    · have hkn : (fun i => -k i) ≠ (0 : FS4Index) := by
        simpa only [← Pi.neg_def, neg_ne_zero] using hk
      have hxy := hcanonical ⟨(fun i => -k i),hkn,hneg⟩
      change x (fun i => -k i) = y (fun i => -k i) at hxy
      rw [hx k, hy k] at hxy
      exact star_injective hxy

theorem fs4HminusFour_measure_ext_of_real_encoding (μ ν : Measure FS4HminusFourCompletion)
    (hμ : ∀ᵐ x ∂μ, x ∈ fs4HminusFourRealCarrier)
    (hν : ∀ᵐ x ∂ν, x ∈ fs4HminusFourRealCarrier)
    (hmap : Measure.map fs4PhysicalCoordinateEncoding μ = Measure.map fs4PhysicalCoordinateEncoding ν) : μ = ν := by
  letI : TopologicalSpace.SeparableSpace FS4HminusFourCompletion := fs4HminusFourCompletion_separable
  apply Measure.ext
  intro A hA
  let B := fs4PhysicalCoordinateEncoding '' (A ∩ fs4HminusFourRealCarrier)
  have hB : MeasurableSet B :=
    (hA.inter fs4HminusFourRealCarrier_closed.measurableSet).image_of_continuousOn_injOn
      fs4PhysicalCoordinateEncoding_continuous.continuousOn
      (fs4PhysicalCoordinateEncoding_injOn.mono Set.inter_subset_right)
  have heq (x : FS4HminusFourCompletion) (hx : x ∈ fs4HminusFourRealCarrier) :
      x ∈ A ↔ x ∈ fs4PhysicalCoordinateEncoding ⁻¹' B := by
    constructor
    · intro ha
      exact ⟨x,⟨ha,hx⟩,rfl⟩
    · rintro ⟨y,⟨hy,hyR⟩,hxy⟩
      have hyx := fs4PhysicalCoordinateEncoding_injOn hyR hx hxy
      simpa only [hyx] using hy
  have hμeq : μ A = μ (fs4PhysicalCoordinateEncoding ⁻¹' B) := by
    apply measure_congr
    filter_upwards [hμ] with x hx
    exact propext (heq x hx)
  have hνeq : ν A = ν (fs4PhysicalCoordinateEncoding ⁻¹' B) := by
    apply measure_congr
    filter_upwards [hν] with x hx
    exact propext (heq x hx)
  rw [hμeq, hνeq, ← Measure.map_apply fs4PhysicalCoordinateEncoding_continuous.measurable hB,
    ← Measure.map_apply fs4PhysicalCoordinateEncoding_continuous.measurable hB, hmap]

end Pphi2Clean.Continuum
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

theorem fs4HminusFour_probabilityMeasure_ext_of_real_finite_marginals
    (μ ν : ProbabilityMeasure FS4HminusFourCompletion)
    (hμ : ∀ᵐ x ∂(μ : Measure FS4HminusFourCompletion), x ∈ fs4HminusFourRealCarrier)
    (hν : ∀ᵐ x ∂(ν : Measure FS4HminusFourCompletion), x ∈ fs4HminusFourRealCarrier)
    (hmarg : ∀ (m : ℕ) (js : Fin m → FS4GaussianRealCoordinateIndex), Function.Injective js →
      μ.map (fs4PhysicalFiniteProjection js) = ν.map (fs4PhysicalFiniteProjection js)) : μ = ν := by
  classical
  apply ProbabilityMeasure.toMeasure_injective
  apply fs4HminusFour_measure_ext_of_real_encoding _ _ hμ hν
  let f := fs4PhysicalCoordinateEncoding
  have hf : Measurable f := fs4PhysicalCoordinateEncoding_continuous.measurable
  letI : IsProbabilityMeasure (Measure.map f (μ : Measure FS4HminusFourCompletion)) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (Measure.map f (ν : Measure FS4HminusFourCompletion)) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  apply ext_of_generate_finite (measurableCylinders (fun _ : FS4GaussianRealCoordinateIndex => ℝ))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro A hA
    obtain ⟨s,S,hS,rfl⟩ := (mem_measurableCylinders A).mp hA
    let e : Fin s.card ≃ s := by simpa using (Fintype.equivFin s).symm
    let js : Fin s.card → FS4GaussianRealCoordinateIndex := fun i => (e i).val
    have hjs : Function.Injective js := Subtype.val_injective.comp e.injective
    let g : EuclideanSpace ℝ (Fin s.card) → (∀ i : s, ℝ) := fun z i => z (e.symm i)
    have hg : Measurable g := by
      apply measurable_pi_lambda
      intro i
      exact ((continuous_apply _).comp (PiLp.continuous_ofLp 2 _)).measurable
    have hproj : (fun x : FS4HminusFourCompletion => s.restrict (f x)) = g ∘ fs4PhysicalFiniteProjection js := by
      funext x i
      change fs4PhysicalRealCoordinate i.val x = fs4PhysicalRealCoordinate (e (e.symm i)).val x
      rw [e.apply_symm_apply]
    have hmap := congrArg (fun ρ : ProbabilityMeasure (EuclideanSpace ℝ (Fin s.card)) =>
      (ρ : Measure (EuclideanSpace ℝ (Fin s.card)))) (hmarg s.card js hjs)
    simp only [ProbabilityMeasure.toMeasure_map] at hmap
    have hmapg := congrArg (Measure.map g) hmap
    rw [Measure.map_map hg (fs4PhysicalFiniteProjection_continuous js).measurable,
      Measure.map_map hg (fs4PhysicalFiniteProjection_continuous js).measurable, ← hproj] at hmapg
    have hv := congrArg (fun ρ : Measure (∀ i : s, ℝ) => ρ S) hmapg
    change (Measure.map (s.restrict ∘ f) (μ : Measure _) ) S = (Measure.map (s.restrict ∘ f) (ν : Measure _)) S at hv
    rw [Measure.map_apply ((Finset.measurable_restrict s).comp hf) hS,
      Measure.map_apply ((Finset.measurable_restrict s).comp hf) hS] at hv
    rw [Measure.map_apply fs4PhysicalCoordinateEncoding_continuous.measurable (hS.cylinder s),
      Measure.map_apply fs4PhysicalCoordinateEncoding_continuous.measurable (hS.cylinder s)]
    exact hv
  · simp

end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

theorem fs4Periodic_subsequence_limit_eq_free (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (ν : ProbabilityMeasure FS4HminusFourCompletion)
    (hν : Tendsto (fun n => fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass (ns n)) atTop (𝓝 ν)) :
    ν = fs4GaussianCarrierProbabilityMeasure L mass := by
  apply fs4HminusFour_probabilityMeasure_ext_of_real_finite_marginals
  · exact fs4Periodic_subsequence_limit_realCarrier_ae L mass hL hmass ns ν hν
  · exact fs4GaussianCarrierMeasure_realCarrier_ae L mass hL hmass
  · intro m js hjs
    exact fs4Periodic_subsequence_limit_finitePhysicalMarginal m L mass hL hmass ns hns ν hν js hjs

theorem fs4PeriodicFixedVolume_weak_tendsto_free (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Tendsto (fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass) atTop
      (𝓝 (fs4GaussianCarrierProbabilityMeasure L mass)) := by
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨ms,ν,hms,hν⟩ := fs4PeriodicFixedVolume_prokhorov_subsequence L mass hL hmass ns hns
  have hνeq := fs4Periodic_subsequence_limit_eq_free L mass hL hmass (ns ∘ ms)
    (hns.comp hms.tendsto_atTop) ν hν
  exact ⟨ms,hνeq ▸ hν⟩

end Pphi2Clean.Continuum
