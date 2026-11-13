import AImathPPhi2Clean.Periodic3DFiniteMarginal
import AImathPPhi2Clean.FiniteRealFamilyMeasure

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

def periodic3DFourierFamilyProjection {m : ℕ} (L : ℝ) (hL : 0 < L)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    Periodic3DCompletion → EuclideanSpace ℝ (Fin m) := fun x =>
  WithLp.toLp 2 (fun i =>
    let z := x (modes i) / (Real.sqrt (periodic3DHminusFourWeight (modes i)) : ℂ)
    if useSine i then z.im else z.re)

theorem continuous_periodic3DFourierFamilyProjection {m : ℕ} (L : ℝ) (hL : 0 < L)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    Continuous (periodic3DFourierFamilyProjection L hL modes useSine) := by
  unfold periodic3DFourierFamilyProjection
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  dsimp
  split
  · exact Complex.continuous_im.comp
      ((periodic3DHminusFour_coordinate_continuous (modes i)).div_const _)
  · exact Complex.continuous_re.comp
      ((periodic3DHminusFour_coordinate_continuous (modes i)).div_const _)

theorem periodic3DFourierCoordinate_finiteSource
    (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)))
    (k : Periodic3DIndex) :
    periodic3DFiniteSourceFourierLift N a L ω k /
      (Real.sqrt (periodic3DHminusFourWeight k) : ℂ) = periodic3DRawAtomicLift N a L hL ω k := by
  have heq := congrFun (periodic3DRawWeightedLift_eq_finiteSourceFourierLift
    N a L ha hL ω) k
  have hsqrt : (Real.sqrt (periodic3DHminusFourWeight k) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ((fs4SobolevWeight_pos 4 (periodic3DExtend k)))).ne'
  calc
    _ = ((Real.sqrt (periodic3DHminusFourWeight k) : ℂ) *
        periodic3DRawAtomicLift N a L hL ω k) /
        (Real.sqrt (periodic3DHminusFourWeight k) : ℂ) := by rw [heq]
    _ = _ := mul_div_cancel_left₀ _ hsqrt

theorem periodic3DFourierFamilyProjection_finiteSource_map
    (m : ℕ) (N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    (periodic3DFiniteSourceGaussianMeasure N (L / (N : ℝ)) mass L
      (div_pos hL (Nat.cast_pos.mpr (NeZero.pos N))) hmass).map
        (periodic3DFourierFamilyProjection L hL modes useSine) =
      physicalFamilyEvalMeasure 3 N m (L / (N : ℝ)) mass
        (div_pos hL (Nat.cast_pos.mpr (NeZero.pos N))) hmass
        (periodic3DFourierTestFamily L hL modes useSine) := by
  let a : ℝ := L / (N : ℝ)
  let ha : 0 < a := div_pos hL (Nat.cast_pos.mpr (NeZero.pos N))
  let H : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)) →
      EuclideanSpace ℝ (Fin m) :=
    fun ω => periodic3DFourierFamilyProjection L hL modes useSine
      (periodic3DFiniteSourceFourierLift N a L ω)
  have hmeasH : Measurable H := (continuous_periodic3DFourierFamilyProjection L hL modes useSine).measurable.comp
    (measurable_periodic3DFiniteSourceFourierLift N a L)
  unfold periodic3DFiniteSourceGaussianMeasure
  rw [Measure.map_map (continuous_periodic3DFourierFamilyProjection L hL modes useSine).measurable
    (measurable_periodic3DFiniteSourceFourierLift N a L)]
  have hmeasEval : Measurable
      (physicalFamilyEvalMap 3 N m a mass ha hmass
        (periodic3DFourierTestFamily L hL modes useSine)) := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.continuous.measurable.comp
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply _).comp (comap_measurable _)
  unfold physicalFamilyEvalMeasure physicalGJMeasure
  rw [Measure.map_map hmeasEval (latticeEmbedLift_measurable (physicalTestEval 3 N a))]
  congr 1
  funext ω
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).injective
  funext i
  change (if useSine i then
      (periodic3DFiniteSourceFourierLift N a L ω (modes i) /
        (Real.sqrt (periodic3DHminusFourWeight (modes i)) : ℂ)).im
    else
      (periodic3DFiniteSourceFourierLift N a L ω (modes i) /
        (Real.sqrt (periodic3DHminusFourWeight (modes i)) : ℂ)).re) =
    (latticeEmbedLift (physicalTestEval 3 N a) ω
      (periodic3DFourierTestFamily L hL modes useSine i))
  have hcoord := periodic3DFourierCoordinate_finiteSource N a L ha hL ω (modes i)
  rw [hcoord]
  by_cases hi : useSine i = true
  · simp [periodic3DFourierTestFamily, periodicFourierTestFamily, hi,
      periodic3DRawAtomicLift, periodic3DComplexFourierLift]
  · have hi' : useSine i = false := Bool.eq_false_of_not_eq_true hi
    simp [periodic3DFourierTestFamily, periodicFourierTestFamily, hi',
      periodic3DRawAtomicLift, periodic3DComplexFourierLift]

theorem periodic3DFixedVolume_fourierFamily_marginal_tendsto
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    Filter.Tendsto
      (fun n : ℕ =>
        (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass n).map
          (periodic3DFourierFamilyProjection L hL modes useSine))
      Filter.atTop
      (nhds (periodicResolventTargetProbabilityMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine))) := by
  have htarget := periodic3DFourierTestFamily_finiteMeasure_tendsto
    m L mass hL hmass modes useSine
  apply Filter.Tendsto.congr' ?_ htarget
  filter_upwards [] with n
  let N := n + 1
  let a : ℝ := L / (N : ℝ)
  have ha : 0 < a := by dsimp [a, N]; exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hseq :
      (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass n).map
          (periodic3DFourierFamilyProjection L hL modes useSine) =
        physicalFamilyEvalProbabilityMeasure 3 N m a mass ha hmass
          (periodic3DFourierTestFamily L hL modes useSine) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    change Measure.map (periodic3DFourierFamilyProjection L hL modes useSine)
        (periodic3DFiniteSourceGaussianMeasure N a mass L ha hmass) = _
    exact periodic3DFourierFamilyProjection_finiteSource_map m N L mass hL hmass modes useSine
  simpa [N, a] using hseq.symm

end Pphi2Clean.Continuum

