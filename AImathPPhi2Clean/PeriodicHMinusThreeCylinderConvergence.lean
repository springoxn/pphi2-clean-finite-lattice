import AImathPPhi2Clean.FiniteFourierCoordinateConvergence
import AImathPPhi2Clean.PeriodicHMinusThreeFourierMeasure
import AImathPPhi2Clean.PeriodicHMinusThreeFixedVolumeTightness
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

noncomputable section

namespace Pphi2Clean.Continuum

open MeasureTheory ProbabilityTheory
open Pphi2Clean.UpstreamLattice

/-- All real tests needed to form a finite list of complex Fourier coordinates. -/
def periodicHMinusThreeCylinderTestFamily (m : ℕ) (L : ℝ) (hperiod : 0 < L)
    (modes : Fin m → PeriodicFourierIndex) :
    Fin (Fintype.card (Fin m × Bool)) → BoundedContinuousFunction (Fin 2 → ℝ) ℝ :=
  fun q =>
    let pair := (Fintype.equivFin (Fin m × Bool)).symm q
    if pair.2 then periodicSineTest 2 L (modes pair.1) hperiod
    else periodicCosineTest 2 L (modes pair.1) hperiod

/-- Reassemble paired real cosine/sine coordinates into weighted complex
Fourier coordinates. -/
def periodicHMinusThreeComplexifyCylinder (m : ℕ)
    (modes : Fin m → PeriodicFourierIndex) :
    EuclideanSpace ℝ (Fin (Fintype.card (Fin m × Bool))) → Fin m → ℂ :=
  fun x i =>
    let e := Fintype.equivFin (Fin m × Bool)
    (Real.sqrt (periodicHMinusThreeWeight (modes i)) : ℂ) *
      ((x (e (i, false)) : ℂ) + (x (e (i, true)) : ℂ) * Complex.I)

theorem continuous_periodicHMinusThreeComplexifyCylinder (m : ℕ)
    (modes : Fin m → PeriodicFourierIndex) :
    Continuous (periodicHMinusThreeComplexifyCylinder m modes) := by
  apply continuous_pi
  intro i
  dsimp [periodicHMinusThreeComplexifyCylinder]
  let e := Fintype.equivFin (Fin m × Bool)
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin (Fintype.card (Fin m × Bool))) =>
      (x (e (i, false)) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_apply (e (i, false))).comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin (Fintype.card (Fin m × Bool)) => ℝ)))
  have hs : Continuous (fun x : EuclideanSpace ℝ (Fin (Fintype.card (Fin m × Bool))) =>
      (x (e (i, true)) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_apply (e (i, true))).comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin (Fintype.card (Fin m × Bool)) => ℝ)))
  exact continuous_const.mul (hc.add (hs.mul_const Complex.I))

theorem measurable_periodicHMinusThreeComplexifyCylinder (m : ℕ)
    (modes : Fin m → PeriodicFourierIndex) :
    Measurable (periodicHMinusThreeComplexifyCylinder m modes) :=
  (continuous_periodicHMinusThreeComplexifyCylinder m modes).measurable

theorem periodicHMinusThreeRawCylinderCoordinate_eq_complexifyFamilyEval
    (N m : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) (modes : Fin m → PeriodicFourierIndex)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)) (i : Fin m) :
    periodicHMinusThreeRawWeightedLift L hperiod ω (modes i) =
      periodicHMinusThreeComplexifyCylinder m modes
        (physicalFamilyEvalMap 2 N
          (Fintype.card (Fin m × Bool)) a mass ha hmass
          (periodicHMinusThreeCylinderTestFamily m L hperiod modes) ω) i := by
  simp [periodicHMinusThreeRawWeightedLift,
    periodicHMinusThreeWeightedCoefficients, periodicComplexFourierLift,
    periodicComplexFourierProbe, periodicHMinusThreeComplexifyCylinder,
    periodicHMinusThreeCylinderTestFamily, physicalFamilyEvalMap,
    Equiv.symm_apply_apply]

/-- The carrier-valued lattice law as a probability measure, conditional on the
named measurability input for its total representative. -/
noncomputable def periodicHMinusThreeLatticeProbabilityMeasure
    (N : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (hinput : PeriodicHMinusThreeLiftMeasureInput N a mass L ha hmass hperiod) :
    ProbabilityMeasure PeriodicHMinusThreeCompletion :=
  ⟨periodicHMinusThreeLatticeMeasure N a mass L ha hmass hperiod, by
    unfold periodicHMinusThreeLatticeMeasure
    exact map_preserves_probability
      (physicalGJMeasure 2 N a mass ha hmass)
      (periodicHMinusThreeTotalCarrierLift L hperiod) hinput.1⟩

theorem periodicHMinusThreeCylinderLaw_eq_complexifiedFamilyLaw
    (N m : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hperiod : 0 < L) (modes : Fin m → PeriodicFourierIndex)
    (hinput : PeriodicHMinusThreeLiftMeasureInput N a mass L ha hmass hperiod) :
    (periodicHMinusThreeLatticeProbabilityMeasure N a mass L ha hmass hperiod hinput).map
        (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
      (physicalFamilyEvalProbabilityMeasure 2 N
        (Fintype.card (Fin m × Bool)) a mass ha hmass
        (periodicHMinusThreeCylinderTestFamily m L hperiod modes)).map
        (f := (periodicHMinusThreeComplexifyCylinder m modes)) ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable) := by
  apply Subtype.ext
  change Measure.map (periodicHMinusThreeCylinderMap m modes)
      (periodicHMinusThreeLatticeMeasure N a mass L ha hmass hperiod) =
    Measure.map (periodicHMinusThreeComplexifyCylinder m modes)
      (physicalFamilyEvalMeasure 2 N (Fintype.card (Fin m × Bool)) a mass ha hmass
        (periodicHMinusThreeCylinderTestFamily m L hperiod modes))
  let μ := physicalGJMeasure 2 N a mass ha hmass
  let lift := periodicHMinusThreeTotalCarrierLift L hperiod
  let eval := physicalFamilyEvalMap 2 N (Fintype.card (Fin m × Bool)) a mass ha hmass
    (periodicHMinusThreeCylinderTestFamily m L hperiod modes)
  let cylinder := periodicHMinusThreeCylinderMap m modes
  let complexify := periodicHMinusThreeComplexifyCylinder m modes
  have hcylinder : Measurable cylinder := by
    dsimp [cylinder]
    exact measurable_periodicHMinusThree_cylinderMap m modes
  have hcomplexify : Measurable complexify := by
    dsimp [complexify]
    exact measurable_periodicHMinusThreeComplexifyCylinder m modes
  have hcoords : (cylinder ∘ lift) =ᵐ[μ] (complexify ∘ eval) := by
    filter_upwards [hinput.2] with ω hω
    funext i
    change lift ω (modes i) = complexify (eval ω) i
    rw [hω (modes i)]
    exact periodicHMinusThreeRawCylinderCoordinate_eq_complexifyFamilyEval
      N m a mass L ha hmass hperiod modes ω i
  calc
    Measure.map cylinder (Measure.map lift μ) = Measure.map (cylinder ∘ lift) μ :=
      AEMeasurable.map_map_of_aemeasurable hcylinder.aemeasurable hinput.1
    _ = Measure.map (complexify ∘ eval) μ := Measure.map_congr hcoords
    _ = Measure.map complexify (Measure.map eval μ) := by
      symm
      exact AEMeasurable.map_map_of_aemeasurable hcomplexify.aemeasurable
        (physicalFamilyEvalMeasure_hasGaussianLaw 2 N
          (Fintype.card (Fin m × Bool)) a mass ha hmass
          (periodicHMinusThreeCylinderTestFamily m L hperiod modes)).aemeasurable

def periodicHMinusThreeLiftMeasureInputAt
    (n : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) : Prop := by
  let N := n + 1
  letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
  exact PeriodicHMinusThreeLiftMeasureInput N (L / (N : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL

/-- Finite-dimensional convergence on the concrete H^-3 cylinders follows by
continuous mapping from Goal 4's finite real Fourier-family convergence. No
whole-carrier weak convergence is asserted. -/
theorem periodicHMinusThreeCylinderProbabilityMeasure_tendsto_of_finite_family
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → PeriodicFourierIndex)
    (hfinite : Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure 2 N
          (Fintype.card (Fin m × Bool)) (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
          (periodicHMinusThreeCylinderTestFamily m L hL modes))
      Filter.atTop
      (nhds (periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes))))
    (hinput : (∀ n : ℕ,
      periodicHMinusThreeLiftMeasureInputAt n L mass hL hmass)) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        (periodicHMinusThreeLatticeProbabilityMeasure N (L / (N : ℝ)) mass L
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL (hinput n)).map
          (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      Filter.atTop
      (nhds ((periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map
        (f := (periodicHMinusThreeComplexifyCylinder m modes)) ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable))) := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ hfinite (continuous_periodicHMinusThreeComplexifyCylinder m modes)
  apply hmap.congr'
  filter_upwards [] with n
  let N := n + 1
  letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
  simpa [N] using (periodicHMinusThreeCylinderLaw_eq_complexifiedFamilyLaw
    N m (L / (N : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL modes (hinput n)).symm

/-- Concrete cylinder convergence obtained directly from Goal 4's finite-family
covariance theorem for the paired cosine/sine tests. -/
theorem periodicHMinusThreeCylinderProbabilityMeasure_tendsto_of_covariance_limits
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → PeriodicFourierIndex)
    (C : BoundedContinuousFunction (Fin 2 → ℝ) ℝ →
      BoundedContinuousFunction (Fin 2 → ℝ) ℝ → ℝ)
    (hinner : ∀ i j : Fin (Fintype.card (Fin m × Bool)), Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites 2 N)))) _
          (numberedLatticeCovarianceGJ 2 N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval 2 N (L / (N : ℝ)))
              (periodicHMinusThreeCylinderTestFamily m L hL modes i)))
          (numberedLatticeCovarianceGJ 2 N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField (physicalTestEval 2 N (L / (N : ℝ)))
              (periodicHMinusThreeCylinderTestFamily m L hL modes j))))
      Filter.atTop (nhds (C
        (periodicHMinusThreeCylinderTestFamily m L hL modes i)
        (periodicHMinusThreeCylinderTestFamily m L hL modes j))))
    (hC : ∀ i j,
      C (periodicHMinusThreeCylinderTestFamily m L hL modes i)
        (periodicHMinusThreeCylinderTestFamily m L hL modes j) =
        periodicResolventCovarianceMatrix 2 (Fintype.card (Fin m × Bool))
          L mass hmass (periodicHMinusThreeCylinderTestFamily m L hL modes) i j)
    (hinput : (∀ n : ℕ,
      periodicHMinusThreeLiftMeasureInputAt n L mass hL hmass)) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        (periodicHMinusThreeLatticeProbabilityMeasure N (L / (N : ℝ)) mass L
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL (hinput n)).map
          (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      Filter.atTop
      (nhds ((periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map
        (f := (periodicHMinusThreeComplexifyCylinder m modes)) ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable))) := by
  apply periodicHMinusThreeCylinderProbabilityMeasure_tendsto_of_finite_family
    m L mass hL hmass modes _ hinput
  exact physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_any_finite_test_family_indexed
    2 (Fintype.card (Fin m × Bool)) L mass hL hmass
    (periodicHMinusThreeCylinderTestFamily m L hL modes) C hinner hC


/-- Under the explicit lift-measure input, the finite-source and lattice laws
have identical finite Fourier cylinder pushforwards. -/
theorem periodicHMinusThreeFiniteSourceCylinderLaw_eq_latticeCylinderLaw
    (N m : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (modes : Fin m → PeriodicFourierIndex)
    (hinput : PeriodicHMinusThreeLiftMeasureInput N a mass L ha hmass hperiod) :
    (periodicHMinusThreeFiniteSourceProbabilityMeasure N a mass L ha hmass hperiod).map
        (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
      (periodicHMinusThreeLatticeProbabilityMeasure N a mass L ha hmass hperiod hinput).map
        (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) := by
  apply Subtype.ext
  change Measure.map (periodicHMinusThreeCylinderMap m modes)
      (Measure.map (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod)
        (finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 2 N a mass ha hmass))) =
    Measure.map (periodicHMinusThreeCylinderMap m modes)
      (periodicHMinusThreeLatticeMeasure N a mass L ha hmass hperiod)
  rw [periodicHMinusThreeFiniteSourceFourierLift_map_eq_latticeMeasure
    N a mass L ha hmass hperiod hinput]
theorem periodicHMinusThreeFiniteSourceCylinderLaw_eq_familyEvalLaw
    (N m : ℕ) [NeZero N] (a mass L : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hperiod : 0 < L)
    (modes : Fin m → PeriodicFourierIndex) :
    (periodicHMinusThreeFiniteSourceProbabilityMeasure N a mass L ha hmass hperiod).map
        (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
      (physicalFamilyEvalProbabilityMeasure 2 N
        (Fintype.card (Fin m × Bool)) a mass ha hmass
        (periodicHMinusThreeCylinderTestFamily m L hperiod modes)).map
        (f := (periodicHMinusThreeComplexifyCylinder m modes)) ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable) := by
  apply Subtype.ext
  change Measure.map (periodicHMinusThreeCylinderMap m modes)
      (Measure.map (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod)
        (finiteCovarianceGaussianMeasure
          (numberedLatticeCovarianceGJ 2 N a mass ha hmass))) =
    Measure.map (periodicHMinusThreeComplexifyCylinder m modes)
      (physicalFamilyEvalMeasure 2 N (Fintype.card (Fin m × Bool)) a mass ha hmass
        (periodicHMinusThreeCylinderTestFamily m L hperiod modes))
  let μ := finiteCovarianceGaussianMeasure
    (numberedLatticeCovarianceGJ 2 N a mass ha hmass)
  let lift := periodicHMinusThreeFiniteSourceFourierLift N a L hperiod
  let cylinder := periodicHMinusThreeCylinderMap m modes
  let embed := latticeEmbedLift (physicalTestEval 2 N a)
  let eval := physicalFamilyEvalMap 2 N (Fintype.card (Fin m × Bool)) a mass ha hmass
    (periodicHMinusThreeCylinderTestFamily m L hperiod modes)
  let complexify := periodicHMinusThreeComplexifyCylinder m modes
  have hcyl : Measurable cylinder := by
    dsimp [cylinder]
    exact measurable_periodicHMinusThree_cylinderMap m modes
  have hlift : Measurable lift := by
    dsimp [lift]
    exact measurable_periodicHMinusThreeFiniteSourceFourierLift N a L hperiod
  have hcomplex : Measurable complexify := by
    dsimp [complexify]
    exact measurable_periodicHMinusThreeComplexifyCylinder m modes
  have heval : AEMeasurable eval (physicalGJMeasure 2 N a mass ha hmass) := by
    dsimp [eval]
    exact (physicalGJMeasure_family_hasGaussianLaw 2 N a mass ha hmass
      (periodicHMinusThreeCylinderTestFamily m L hperiod modes)).aemeasurable
  have hembed : Measurable embed := by
    dsimp [embed]
    exact latticeEmbedLift_measurable (physicalTestEval 2 N a)
  have hpoint : cylinder ∘ lift = complexify ∘ eval ∘ embed := by
    funext ω
    funext i
    change periodicHMinusThreeCylinderMap m modes
      (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω) i = _
    rw [periodicHMinusThreeCylinderMap_apply]
    have hseq := periodicHMinusThreeRawWeightedLift_eq_finiteSourceFourierLift
      N a L ha hperiod ω
    have hmem : Memℓp (periodicHMinusThreeRawWeightedLift L hperiod
        (latticeEmbedLift (physicalTestEval 2 N a) ω)) 2 := by
      rw [hseq]
      exact lp.memℓp (periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω)
    have hcarrier := periodicHMinusThreeFiniteSourceFourierLift_eq_totalCarrierLift
      N a L ha hperiod ω
    have hcoord : periodicHMinusThreeFiniteSourceFourierLift N a L hperiod ω (modes i) =
        periodicHMinusThreeTotalCarrierLift L hperiod
          (latticeEmbedLift (physicalTestEval 2 N a) ω) (modes i) := by
      exact congrArg (fun x : PeriodicHMinusThreeCompletion => x (modes i)) hcarrier
    rw [hcoord]
    have hraw : periodicHMinusThreeTotalCarrierLift L hperiod
        (latticeEmbedLift (physicalTestEval 2 N a) ω) (modes i) =
        periodicHMinusThreeRawWeightedLift L hperiod
          (latticeEmbedLift (physicalTestEval 2 N a) ω) (modes i) := by
      simp [periodicHMinusThreeTotalCarrierLift, dif_pos hmem]
    rw [hraw]
    exact periodicHMinusThreeRawCylinderCoordinate_eq_complexifyFamilyEval
      N m a mass L ha hmass hperiod modes
      (latticeEmbedLift (physicalTestEval 2 N a) ω) i
  rw [Measure.map_map hcyl hlift]
  rw [show physicalFamilyEvalMeasure 2 N (Fintype.card (Fin m × Bool)) a mass ha hmass
      (periodicHMinusThreeCylinderTestFamily m L hperiod modes) =
      Measure.map eval (physicalGJMeasure 2 N a mass ha hmass) by rfl]
  rw [show physicalGJMeasure 2 N a mass ha hmass = Measure.map embed μ by rfl]
  have heval' : AEMeasurable eval (Measure.map embed μ) := by
    simpa [physicalGJMeasure, μ] using heval
  rw [AEMeasurable.map_map_of_aemeasurable heval' hembed.aemeasurable]
  have hevalcomp : AEMeasurable (eval ∘ embed) μ :=
    heval'.comp_aemeasurable hembed.aemeasurable
  rw [AEMeasurable.map_map_of_aemeasurable hcomplex.aemeasurable hevalcomp]
  rw [Measure.map_congr (Filter.Eventually.of_forall (fun x => congrFun hpoint x))]

/-- The finite-family convergence theorem applies directly to the finite-source
pushforward cylinder laws; no total-carrier measurability input is needed. -/
theorem periodicHMinusThreeFiniteSourceCylinderProbabilityMeasure_tendsto_of_finite_family
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → PeriodicFourierIndex)
    (hfinite : Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure 2 N
          (Fintype.card (Fin m × Bool)) (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
          (periodicHMinusThreeCylinderTestFamily m L hL modes))
      Filter.atTop
      (nhds (periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)))) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        (periodicHMinusThreeFiniteSourceProbabilityMeasure N
          (L / (N : ℝ)) mass L
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL).map
          (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      Filter.atTop
      (nhds ((periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map
        (f := (periodicHMinusThreeComplexifyCylinder m modes)) ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable))) := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ hfinite (continuous_periodicHMinusThreeComplexifyCylinder m modes)
  apply hmap.congr'
  filter_upwards [] with n
  let N := n + 1
  letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
  exact (periodicHMinusThreeFiniteSourceCylinderLaw_eq_familyEvalLaw
    N m (L / (N : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL modes).symm
theorem periodicCosineTest_isFlatTorusPeriodic
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

theorem periodicSineTest_isFlatTorusPeriodic
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

theorem periodicHMinusThreeCylinderTestFamily_isFlatTorusPeriodic
    (m : ℕ) (L : ℝ) (hL : 0 < L) (modes : Fin m → PeriodicFourierIndex) :
    ∀ q, IsFlatTorusPeriodic 2 L
      (periodicHMinusThreeCylinderTestFamily m L hL modes q) := by
  intro q x i
  dsimp [periodicHMinusThreeCylinderTestFamily]
  split_ifs with h
  · exact periodicSineTest_isFlatTorusPeriodic 2 L hL (modes ((Fintype.equivFin
      (Fin m × Bool)).symm q).1) x i
  · exact periodicCosineTest_isFlatTorusPeriodic 2 L hL (modes ((Fintype.equivFin
      (Fin m × Bool)).symm q).1) x i

/-- The actual fixed-volume Fourier covariance limit supplies convergence of
all entries in the finite paired cosine/sine family, without a universal test
function covariance hypothesis. -/
theorem periodicHMinusThreeFiniteSourceCylinderProbabilityMeasure_tendsto_fixedVolume
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → PeriodicFourierIndex) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        (periodicHMinusThreeFiniteSourceProbabilityMeasure N
          (L / (N : ℝ)) mass L
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL).map
          (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      Filter.atTop
      (nhds ((periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map
        (f := (periodicHMinusThreeComplexifyCylinder m modes)) ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable))) := by
  let fs := periodicHMinusThreeCylinderTestFamily m L hL modes
  let C : BoundedContinuousFunction (Fin 2 → ℝ) ℝ →
      BoundedContinuousFunction (Fin 2 → ℝ) ℝ → ℝ :=
    fun f g => (physicalTorusResolventPairing 2 L mass hmass f g).re
  have hinner : ∀ i j : Fin (Fintype.card (Fin m × Bool)), Filter.Tendsto
      (fun n : ℕ => fixedVolumeCovarianceInner 2 L mass hL hmass (fs i) (fs j) n)
      Filter.atTop (nhds (C (fs i) (fs j))) := by
    intro i j
    simpa [C] using fixedVolumeCovarianceInner_tendsto_periodicMassiveResolvent
      2 L mass hL hmass (fs i) (fs j)
      (periodicHMinusThreeCylinderTestFamily_isFlatTorusPeriodic m L hL modes i)
      (periodicHMinusThreeCylinderTestFamily_isFlatTorusPeriodic m L hL modes j)
  have hC : ∀ i j, C (fs i) (fs j) =
      periodicResolventCovarianceMatrix 2 (Fintype.card (Fin m × Bool))
        L mass hmass fs i j := by
    intro i j
    rfl
  have hfinite := physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_any_finite_test_family_indexed
    2 (Fintype.card (Fin m × Bool)) L mass hL hmass fs C hinner hC
  exact periodicHMinusThreeFiniteSourceCylinderProbabilityMeasure_tendsto_of_finite_family
    m L mass hL hmass modes hfinite

theorem periodicHMinusThreeFixedVolumeMeasureSequence_cylinder_tendsto
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → PeriodicFourierIndex) :
    Filter.Tendsto
      (fun n : ℕ =>
        (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
          L mass hL hmass n).map (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      Filter.atTop
      (nhds ((periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map
        (f := (periodicHMinusThreeComplexifyCylinder m modes)) ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable))) := by
  have hbase := periodicHMinusThreeFiniteSourceCylinderProbabilityMeasure_tendsto_fixedVolume
    m L mass hL hmass modes
  apply hbase.congr'
  filter_upwards [] with n
  let N := n + 1
  let a := L / (N : ℝ)
  have heq : periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure L mass hL hmass n =
      periodicHMinusThreeFiniteSourceProbabilityMeasure N a mass L
        (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL := by
    apply Subtype.ext
    rfl
  exact congrArg (fun μ : ProbabilityMeasure PeriodicHMinusThreeCompletion =>
    μ.map (f := (periodicHMinusThreeCylinderMap m modes)) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable)) heq

end Pphi2Clean.Continuum

