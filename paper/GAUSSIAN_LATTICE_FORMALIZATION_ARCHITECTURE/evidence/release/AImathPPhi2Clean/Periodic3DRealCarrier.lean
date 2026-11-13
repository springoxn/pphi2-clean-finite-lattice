import AImathPPhi2Clean.Periodic3DGaussianTarget
import AImathPPhi2Clean.Periodic3DAtomicMarginal

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology Pphi2Clean.UpstreamLattice

def periodic3DHminusFourRealCarrier : Set Periodic3DCompletion :=
  {x | ∀ k, x (-k) = star (x k)}

theorem periodic3DHminusFourRealCarrier_closed :
    IsClosed periodic3DHminusFourRealCarrier := by
  rw [show periodic3DHminusFourRealCarrier = ⋂ k : Periodic3DIndex,
      {x : Periodic3DCompletion | x (-k) = star (x k)} by
    ext x
    simp [periodic3DHminusFourRealCarrier]]
  exact isClosed_iInter (fun k => isClosed_eq
    (periodic3DHminusFour_coordinate_continuous (-k))
    ((periodic3DHminusFour_coordinate_continuous k).star))

theorem periodic3DExtend_neg (k : Periodic3DIndex) :
    periodic3DExtend (-k) = -periodic3DExtend k := by
  funext i
  by_cases h : i.val < 3 <;> simp [periodic3DExtend, h]

theorem periodic3DSobolevWeight_neg (s : ℝ) (k : Periodic3DIndex) :
    periodic3DSobolevWeight s (-k) = periodic3DSobolevWeight s k := by
  unfold periodic3DSobolevWeight
  rw [periodic3DExtend_neg]
  exact fs4SobolevWeight_neg s _

theorem periodic3DHminusFourWeight_neg (k : Periodic3DIndex) :
    periodic3DHminusFourWeight (-k) = periodic3DHminusFourWeight k :=
  periodic3DSobolevWeight_neg 4 k

theorem periodic3DSitePhase_neg (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) (k : Periodic3DIndex) :
    periodic3DSitePhase N a L j (-k) = -periodic3DSitePhase N a L j k := by
  simp [periodic3DSitePhase, Finset.sum_neg_distrib, mul_neg]

theorem periodic3DSiteSequence_neg (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) (k : Periodic3DIndex) :
    periodic3DSiteSequence N a L j (-k) = star (periodic3DSiteSequence N a L j k) := by
  apply Complex.ext <;> simp [periodic3DSiteSequence, periodic3DSitePhase_neg, Real.cos_neg, Real.sin_neg]

theorem periodic3DSiteWeightedSequence_neg (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) (k : Periodic3DIndex) :
    periodic3DSiteWeightedSequence N a L j (-k) =
      star (periodic3DSiteWeightedSequence N a L j k) := by
  simp [periodic3DSiteWeightedSequence, periodic3DHminusFourWeight_neg,
    periodic3DSiteSequence_neg]

theorem periodic3DFiniteSourceFourierLift_mem_realCarrier
    (N : ℕ) [NeZero N] (a L : ℝ) (_ha : 0 < a) (_hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DFiniteSourceFourierLift N a L ω ∈ periodic3DHminusFourRealCarrier := by
  intro k
  simp [periodic3DFiniteSourceFourierLift_apply, periodic3DSiteWeightedSequence_neg]

theorem periodic3DFiniteSourceGaussianMeasure_realCarrier_ae
    (N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : 0 < L) :
    ∀ᵐ x ∂periodic3DFiniteSourceGaussianMeasure N a mass L ha hmass,
      x ∈ periodic3DHminusFourRealCarrier := by
  unfold periodic3DFiniteSourceGaussianMeasure
  apply (ae_map_iff (measurable_periodic3DFiniteSourceFourierLift N a L).aemeasurable
    periodic3DHminusFourRealCarrier_closed.measurableSet).2
  exact Eventually.of_forall (fun ω =>
    periodic3DFiniteSourceFourierLift_mem_realCarrier N a L ha hL ω)

theorem periodic3DFixedVolume_realCarrier_ae
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (n : ℕ) :
    ∀ᵐ x ∂(periodic3DFixedVolumeProbabilityMeasure L mass hL hmass n :
      Measure Periodic3DCompletion), x ∈ periodic3DHminusFourRealCarrier := by
  exact periodic3DFiniteSourceGaussianMeasure_realCarrier_ae (n+1)
    (L / ((n+1 : ℕ) : ℝ)) mass L
    (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass hL

theorem periodic3DRestrictFourier_mem_realCarrier
    (x : FS4HminusFourCompletion) (hx : x ∈ fs4HminusFourRealCarrier) :
    periodic3DRestrictFourier x ∈ periodic3DHminusFourRealCarrier := by
  intro k
  change x (periodic3DExtend (-k)) = star (x (periodic3DExtend k))
  rw [periodic3DExtend_neg]
  exact hx (periodic3DExtend k)

theorem periodic3DTargetMap_mem_realCarrier (L : ℝ)
    (x : FS4HminusFourCompletion) (hx : x ∈ fs4HminusFourRealCarrier) :
    periodic3DTargetMap L x ∈ periodic3DHminusFourRealCarrier := by
  intro k
  simp only [periodic3DTargetMap_apply, periodic3DExtend_neg]
  have hh : x (-periodic3DExtend k) = star (x (periodic3DExtend k)) := hx (periodic3DExtend k)
  rw [hh]
  simp [Complex.real_smul]

theorem periodic3DGaussianTargetMeasure_realCarrier_ae
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∀ᵐ x ∂periodic3DGaussianTargetMeasure L mass,
      x ∈ periodic3DHminusFourRealCarrier := by
  unfold periodic3DGaussianTargetMeasure
  apply (ae_map_iff (continuous_periodic3DTargetMap L).measurable.aemeasurable
    periodic3DHminusFourRealCarrier_closed.measurableSet).2
  filter_upwards [fs4GaussianCarrierMeasure_realCarrier_ae L mass hL hmass] with x hx
  exact periodic3DTargetMap_mem_realCarrier L x hx

theorem periodic3DHminusFour_realCarrier_ae_of_weak_tendsto
    (μs : ℕ → ProbabilityMeasure Periodic3DCompletion)
    (ν : ProbabilityMeasure Periodic3DCompletion) (hν : Tendsto μs atTop (𝓝 ν))
    (hs : ∀ n, ∀ᵐ x ∂(μs n : Measure Periodic3DCompletion),
      x ∈ periodic3DHminusFourRealCarrier) :
    ∀ᵐ x ∂(ν : Measure Periodic3DCompletion), x ∈ periodic3DHminusFourRealCarrier := by
  let : TopologicalSpace.SeparableSpace Periodic3DCompletion :=
    periodic3DHminusFourCompletion_separable
  have hzero (n : ℕ) :
      (μs n : Measure Periodic3DCompletion) periodic3DHminusFourRealCarrierᶜ = 0 :=
    ae_iff.mp (hs n)
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν
    periodic3DHminusFourRealCarrier_closed.isOpen_compl
  have hle0 : (ν : Measure Periodic3DCompletion) periodic3DHminusFourRealCarrierᶜ ≤ 0 := by
    simpa only [hzero, liminf_const] using hle
  exact ae_iff.mpr (le_antisymm hle0 bot_le)

theorem periodic3D_subsequence_limit_realCarrier_ae
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (ν : ProbabilityMeasure Periodic3DCompletion)
    (hν : Tendsto (fun n => periodic3DFixedVolumeProbabilityMeasure L mass hL hmass (ns n))
      atTop (𝓝 ν)) :
    ∀ᵐ x ∂(ν : Measure Periodic3DCompletion), x ∈ periodic3DHminusFourRealCarrier :=
  periodic3DHminusFour_realCarrier_ae_of_weak_tendsto _ ν hν
    (fun n => periodic3DFixedVolume_realCarrier_ae L mass hL hmass (ns n))

end Pphi2Clean.Continuum

#print axioms Pphi2Clean.Continuum.periodic3DFiniteSourceFourierLift_mem_realCarrier
#print axioms Pphi2Clean.Continuum.periodic3DFixedVolume_realCarrier_ae
#print axioms Pphi2Clean.Continuum.periodic3DGaussianTargetMeasure_realCarrier_ae
#print axioms Pphi2Clean.Continuum.periodic3DHminusFour_realCarrier_ae_of_weak_tendsto
#print axioms Pphi2Clean.Continuum.periodic3D_subsequence_limit_realCarrier_ae
