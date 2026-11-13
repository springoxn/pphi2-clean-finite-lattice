import AImathPPhi2Clean.ArbitraryDimParameters
import AImathPPhi2Clean.TargetCylinderArbitraryDim
import AImathPPhi2Clean.FiniteFourierCoordinateConvergence

set_option maxRecDepth 500000
set_option maxHeartbeats 0
noncomputable section
namespace Pphi2Clean.ArbitraryDimGaussian
open Pphi2Clean.ArbitraryDim
variable [Parameters]
open MeasureTheory ProbabilityTheory Topology Filter
open Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice

def targetFourierEnumeration (s : Finset Index) : (s × Bool) ≃ Fin (Fintype.card (s × Bool)) :=
  Fintype.equivFin _

def targetRealFourierFamily (s : Finset Index) (L : ℝ) (hL : 0 < L) :=
  periodicFourierTestFamily dimension (Fintype.card (s × Bool)) L hL
    (fun j => ((targetFourierEnumeration s).symm j).1.val)
    (fun j => ((targetFourierEnumeration s).symm j).2)

def targetReconstructFinite (s : Finset Index)
    (z : EuclideanSpace ℝ (Fin (Fintype.card (s × Bool)))) : s → ℂ :=
  fun k => (Real.sqrt (targetWeight k.val) : ℂ) *
    ((z (targetFourierEnumeration s (k, false)) : ℂ) +
      (z (targetFourierEnumeration s (k, true)) : ℂ) * Complex.I)

theorem continuous_targetReconstructFinite (s : Finset Index) :
    Continuous (targetReconstructFinite s) := by
  apply continuous_pi
  intro k
  apply continuous_const.mul
  apply Continuous.add
  · exact Complex.continuous_ofReal.comp (EuclideanSpace.proj (targetFourierEnumeration s (k, false))).continuous
  · exact (Complex.continuous_ofReal.comp
      (EuclideanSpace.proj (targetFourierEnumeration s (k, true))).continuous).mul continuous_const

def targetFiniteGaussianLimit (s : Finset Index) (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) : ProbabilityMeasure (s → ℂ) :=
  (periodicResolventTargetProbabilityMeasure dimension (Fintype.card (s × Bool)) L mass hmass
    (targetRealFourierFamily s L hL)).map (targetReconstructFinite s)

theorem targetFiniteCoordinates_actualTargetLift (s : Finset Index) (N : ℕ) [NeZero N]
    (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) (ξ : FiniteConfig N) :
    targetFiniteCoordinates s (actualTargetLift N a L ha hL ξ) =
      targetReconstructFinite s
        (physicalFamilyEvalMap dimension N (Fintype.card (s × Bool)) a mass ha hmass
          (targetRealFourierFamily s L hL)
          (latticeEmbedLift (physicalTestEval dimension N a) ξ)) := by
  funext k
  change actualTargetLift N a L ha hL ξ k = _
  rw [actualTargetLift_apply]
  simp [targetReconstructFinite, targetRealFourierFamily, periodicFourierTestFamily,
    physicalFamilyEvalMap, rawFourierProbe, actualRawAtomicLift]

theorem target_finite_marginal_eq_reconstructed_physical_family (s : Finset Index)
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hL : 0 < L) :
    (actualTargetProbabilityMeasure N a mass L ha hmass hL).map (targetFiniteCoordinates s) =
      (physicalFamilyEvalProbabilityMeasure dimension N (Fintype.card (s × Bool)) a mass ha hmass
        (targetRealFourierFamily s L hL)).map (targetReconstructFinite s) := by
  apply Subtype.ext
  have hfamily : Measurable (physicalFamilyEvalMap dimension N (Fintype.card (s × Bool))
      a mass ha hmass (targetRealFourierFamily s L hL)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (Fintype.card (s × Bool)) => ℝ)).measurable.comp
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (targetRealFourierFamily s L hL j)).comp (comap_measurable _)
  change Measure.map (targetFiniteCoordinates s)
      (Measure.map (actualTargetLift N a L ha hL)
        (finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ dimension N a mass ha hmass))) =
    Measure.map (targetReconstructFinite s)
      (Measure.map (physicalFamilyEvalMap dimension N (Fintype.card (s × Bool)) a mass ha hmass
        (targetRealFourierFamily s L hL))
        (Measure.map (latticeEmbedLift (physicalTestEval dimension N a))
          (finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ dimension N a mass ha hmass))))
  rw [Measure.map_map (continuous_targetFiniteCoordinates s).measurable
    (measurable_actualTargetLift N a L ha hL)]
  rw [Measure.map_map hfamily (latticeEmbedLift_measurable (physicalTestEval dimension N a))]
  rw [Measure.map_map (continuous_targetReconstructFinite s).measurable
    (hfamily.comp (latticeEmbedLift_measurable (physicalTestEval dimension N a)))]
  congr 1
  funext ξ
  exact targetFiniteCoordinates_actualTargetLift s N a mass L ha hmass hL ξ

theorem actualTarget_fixedVolume_finite_marginal_tendsto
    (s : Finset Index) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Tendsto (fun n => (actualTargetProbabilityMeasure_fixedVolume L mass hL hmass n).map
      (targetFiniteCoordinates s)) atTop (𝓝 (targetFiniteGaussianLimit s L mass hL hmass)) := by
  have hp := physicalPeriodicFourierFamilyProbabilityMeasure_fixedVolume_tendsto
    dimension (Fintype.card (s × Bool)) L mass hL hmass
    (fun j => ((targetFourierEnumeration s).symm j).1.val)
    (fun j => ((targetFourierEnumeration s).symm j).2)
  have hh := (ProbabilityMeasure.continuous_map (continuous_targetReconstructFinite s)).continuousAt.tendsto.comp hp
  apply hh.congr'
  apply Filter.Eventually.of_forall
  intro n
  exact (target_finite_marginal_eq_reconstructed_physical_family s (n + 1)
    (L / ((n + 1 : ℕ) : ℝ)) mass L (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n)))
    hmass hL).symm

def targetReconstructFiniteCLM (s : Finset Index) :
    EuclideanSpace ℝ (Fin (Fintype.card (s × Bool))) →L[ℝ] (s → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := targetReconstructFinite s
      map_add' := by
        intro x y
        funext k
        simp only [targetReconstructFinite, PiLp.add_apply, Complex.ofReal_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c x
        funext k
        simp only [targetReconstructFinite, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
          Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
        ring }

theorem targetFiniteGaussianLimit_isGaussian (s : Finset Index) (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) :
    IsGaussian (targetFiniteGaussianLimit s L mass hL hmass : Measure (s → ℂ)) := by
  have hg := periodicResolventTargetMeasure_hasGaussianLaw dimension (Fintype.card (s × Bool))
    L mass hmass (targetRealFourierFamily s L hL)
  letI : IsGaussian (periodicResolventTargetMeasure dimension (Fintype.card (s × Bool)) L mass hmass
      (targetRealFourierFamily s L hL)) := by
    simpa only [Measure.map_id] using hg.isGaussian_map
  change IsGaussian (Measure.map (targetReconstructFiniteCLM s)
    (periodicResolventTargetMeasure dimension (Fintype.card (s × Bool)) L mass hmass
      (targetRealFourierFamily s L hL)))
  infer_instance

#print axioms targetFiniteGaussianLimit_isGaussian
#print axioms actualTarget_fixedVolume_finite_marginal_tendsto
end Pphi2Clean.ArbitraryDimGaussian
