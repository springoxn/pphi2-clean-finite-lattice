import AImathPPhi2Clean.InfiniteGaussianNoise
import AImathPPhi2Clean.WeakDualReconstruction
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory Topology ProbabilityTheory
open Pphi2Clean.GaussianField

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- The cylindrical sigma-algebra on continuous linear configurations. -/
instance instMeasurableSpaceWeakDual : MeasurableSpace (WeakDual ℝ E) :=
  MeasurableSpace.comap (fun ω f => ω f) MeasurableSpace.pi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]

/-- Limit of the finite Hilbert-valued Gaussian sums; `limUnder` supplies a
canonical value even on the null set where the sequence does not converge. -/
def gaussianHilbertSeriesLimit (v : ℕ → H) (ξ : ℕ → ℝ) : H :=
  Filter.limUnder Filter.atTop (fun N =>
    ∑ n ∈ Finset.range N, ξ n • v n)

theorem gaussianHilbertSeriesLimit_stronglyMeasurable (v : ℕ → H) :
    StronglyMeasurable (gaussianHilbertSeriesLimit v) := by
  apply StronglyMeasurable.limUnder
  intro N
  have hsum : (fun ξ : ℕ → ℝ =>
      ∑ n ∈ Finset.range N, ξ n • v n) =
      ∑ n ∈ Finset.range N, (fun ξ : ℕ → ℝ => ξ n • v n) := by
    funext ξ
    simp
  rw [hsum]
  apply Finset.stronglyMeasurable_sum
  intro n hn
  exact ((measurable_pi_apply n).stronglyMeasurable).smul_const (v n)

/-- The Gaussian Hilbert series induces a measurable configuration map. -/
def gaussianSeriesConfiguration (J : E →L[ℝ] H) (v : ℕ → H)
    (ξ : ℕ → ℝ) : WeakDual ℝ E :=
  hilbertVectorConfiguration J (gaussianHilbertSeriesLimit v ξ)

theorem gaussianSeriesConfiguration_measurable (J : E →L[ℝ] H) (v : ℕ → H) :
    Measurable (gaussianSeriesConfiguration J v) := by
  rw [measurable_iff_comap_le]
  show (MeasurableSpace.comap (fun ω f => ω f) MeasurableSpace.pi).comap
      (gaussianSeriesConfiguration J v) ≤ _
  rw [MeasurableSpace.comap_comp]
  apply (measurable_pi_lambda _ ?_).comap_le
  intro f
  change Measurable (fun ξ : ℕ → ℝ =>
    @inner ℝ H _ (gaussianHilbertSeriesLimit v ξ) (J f))
  have hlimit : Measurable (gaussianHilbertSeriesLimit v) :=
    (gaussianHilbertSeriesLimit_stronglyMeasurable v).measurable
  have hEval : Measurable (fun ξ : ℕ → ℝ =>
      (innerSL ℝ (J f)) (gaussianHilbertSeriesLimit v ξ)) :=
    ((innerSL ℝ (J f)).continuous.measurable).comp hlimit
  convert hEval using 1
  funext ξ
  simp only [innerSL_apply_apply]
  exact real_inner_comm _ _

def gaussianWeakDualMeasure (J : E →L[ℝ] H) (v : ℕ → H) :
    Measure (WeakDual ℝ E) :=
  Measure.map (gaussianSeriesConfiguration J v) (gaussianNoiseMeasure 1)

instance gaussianWeakDualMeasure_isProbability (J : E →L[ℝ] H) (v : ℕ → H) :
    IsProbabilityMeasure (gaussianWeakDualMeasure J v) := by
  unfold gaussianWeakDualMeasure
  infer_instance


theorem gaussianHilbertSeriesLimit_eq_tsum_ae (v : ℕ → H)
    (hv : Summable (fun n => ‖v n‖)) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      gaussianHilbertSeriesLimit v ξ = ∑' n, ξ n • v n := by
  filter_upwards [gaussianNoiseMeasure_hilbert_series_summable_ae v hv] with ξ hξ
  have ht : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, ξ n • v n)
      Filter.atTop (𝓝 (∑' n, ξ n • v n)) := hξ.hasSum.tendsto_sum_nat
  change Filter.limUnder Filter.atTop
    (fun N => ∑ n ∈ Finset.range N, ξ n • v n) = _
  exact ht.limUnder_eq


theorem gaussianSeriesConfiguration_eval_eq_tsum_ae (J : E →L[ℝ] H)
    (v : ℕ → H) (hv : Summable (fun n => ‖v n‖)) (f : E) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      gaussianSeriesConfiguration J v ξ f =
        ∑' n, ξ n * @inner ℝ H _ (v n) (J f) := by
  filter_upwards [gaussianHilbertSeriesLimit_eq_tsum_ae v hv,
    gaussianNoiseMeasure_hilbert_series_summable_ae v hv] with ξ hξ hsum
  change @inner ℝ H _ (gaussianHilbertSeriesLimit v ξ) (J f) = _
  rw [hξ]
  have hmap := (innerSL ℝ (J f)).map_tsum hsum
  rw [real_inner_comm]
  change @inner ℝ H _ (J f) (∑' n, ξ n • v n) = _ at hmap
  rw [hmap]
  simp_rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]

theorem gaussianSeriesConfiguration_coeff_summable (J : E →L[ℝ] H)
    (v : ℕ → H) (hv : Summable (fun n => ‖v n‖)) (f : E) :
    Summable (fun n => |@inner ℝ H _ (v n) (J f)|) := by
  have hdom : Summable (fun n => ‖J f‖ * ‖v n‖) := hv.mul_left _
  apply Summable.of_norm_bounded hdom
  intro n
  simpa only [Real.norm_eq_abs, abs_abs] using
    (abs_real_inner_le_norm (v n) (J f)).trans_eq (mul_comm _ _)

theorem gaussianSeriesConfiguration_eval_series_summable_ae
    (J : E →L[ℝ] H) (v : ℕ → H) (hv : Summable (fun n => ‖v n‖))
    (f : E) : ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      Summable (fun n => ξ n * @inner ℝ H _ (v n) (J f)) := by
  have hc := gaussianSeriesConfiguration_coeff_summable J v hv f
  exact gaussianNoiseMeasure_series_summable_ae
    (fun n => @inner ℝ H _ (v n) (J f)) hc


theorem gaussianSeriesConfiguration_eval_L2_norm_bound
    (J : E →L[ℝ] H) (v : ℕ → H) (hv : Summable (fun n => ‖v n‖))
    (f : E) :
    ‖∑' n, (((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul
        (@inner ℝ H _ (v n) (J f))).toLp
          (fun ξ : ℕ → ℝ => @inner ℝ H _ (v n) (J f) * ξ n))‖ ≤
      (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
        (‖J f‖ * ∑' n, ‖v n‖) := by
  let c : ℕ → ℝ := fun n => @inner ℝ H _ (v n) (J f)
  have hc : Summable (fun n => |c n|) :=
    gaussianSeriesConfiguration_coeff_summable J v hv f
  have hmajor : Summable (fun n => ‖J f‖ * ‖v n‖) := hv.mul_left _
  have hterm : ∀ n, |c n| ≤ ‖J f‖ * ‖v n‖ := by
    intro n
    simpa [c, mul_comm] using abs_real_inner_le_norm (v n) (J f)
  have hsum : ∑' n, |c n| ≤ ‖J f‖ * ∑' n, ‖v n‖ := by
    calc
      ∑' n, |c n| ≤ ∑' n, ‖J f‖ * ‖v n‖ := hc.tsum_le_tsum hterm hmajor
      _ = ‖J f‖ * ∑' n, ‖v n‖ := tsum_mul_left
  have hgauss : 0 ≤
      (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal :=
    ENNReal.toReal_nonneg
  calc
    ‖∑' n, (((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul
        (c n)).toLp (fun ξ : ℕ → ℝ => c n * ξ n))‖ ≤
      (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal * ∑' n, |c n| :=
        gaussianNoiseMeasure_series_L2_norm_le_of_abs_summable c hc
    _ ≤ (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
        (‖J f‖ * ∑' n, ‖v n‖) := mul_le_mul_of_nonneg_left hsum hgauss


theorem gaussianSeriesConfiguration_eval_L2_hasSum_ae
    (J : E →L[ℝ] H) (v : ℕ → H) (hv : Summable (fun n => ‖v n‖))
    (f : E) : ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      HasSum (fun n => @inner ℝ H _ (v n) (J f) * ξ n)
        ((∑' n, (((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul
          (@inner ℝ H _ (v n) (J f))).toLp
            (fun ξ : ℕ → ℝ => @inner ℝ H _ (v n) (J f) * ξ n))) ξ) := by
  exact gaussianNoiseMeasure_series_L2_hasSum_of_abs_summable
    (fun n => @inner ℝ H _ (v n) (J f))
    (gaussianSeriesConfiguration_coeff_summable J v hv f)


theorem gaussianWeakDualMeasure_eval_L2_norm_bound
    (J : E →L[ℝ] H) (v : ℕ → H) (hv : Summable (fun n => ‖v n‖))
    (f : E) :
    (eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal)
      (gaussianWeakDualMeasure J v)).toReal ≤
      (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
        (‖J f‖ * ∑' n, ‖v n‖) := by
  let μ := gaussianNoiseMeasure 1
  let F := gaussianSeriesConfiguration J v
  let c : ℕ → ℝ := fun n => @inner ℝ H _ (v n) (J f)
  let S : Lp ℝ 2 μ := ∑' n,
    (((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul (c n)).toLp
      (fun ξ : ℕ → ℝ => c n * ξ n))
  have hpres : MeasurePreserving F μ (gaussianWeakDualMeasure J v) := by
    unfold gaussianWeakDualMeasure
    exact ⟨gaussianSeriesConfiguration_measurable J v, rfl⟩
  have hEval : Measurable (fun ω : WeakDual ℝ E => ω f) := by
    change Measurable (fun ω : WeakDual ℝ E => (ω : E → ℝ) f)
    exact (measurable_pi_apply f).comp (comap_measurable _)
  have hcomp : eLpNorm ((fun ω : WeakDual ℝ E => ω f) ∘ F) (2 : ENNReal) μ =
      eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal)
        (gaussianWeakDualMeasure J v) :=
    eLpNorm_comp_measurePreserving hEval.aestronglyMeasurable hpres
  have hconf : ∀ᵐ ξ ∂μ, F ξ f = ∑' n, ξ n * c n := by
    simpa [F, c] using gaussianSeriesConfiguration_eval_eq_tsum_ae J v hv f
  have hseries : ∀ᵐ ξ ∂μ, HasSum (fun n => c n * ξ n) (S ξ) := by
    simpa [c, S] using gaussianSeriesConfiguration_eval_L2_hasSum_ae J v hv f
  have hae : (fun ξ => F ξ f) =ᵐ[μ] fun ξ => S ξ := by
    filter_upwards [hconf, hseries] with ξ hconf hseries
    calc
      F ξ f = ∑' n, ξ n * c n := hconf
      _ = ∑' n, c n * ξ n := by
        apply tsum_congr
        intro n
        ring
      _ = S ξ := hseries.tsum_eq
  have hS_mem : MemLp (fun ξ : ℕ → ℝ => S ξ) (2 : ENNReal) μ := Lp.memLp S
  have hS_toLp : MemLp.toLp (fun ξ : ℕ → ℝ => S ξ) hS_mem = S :=
    Lp.toLp_coeFn S hS_mem
  have hSnorm : (eLpNorm (fun ξ : ℕ → ℝ => S ξ) (2 : ENNReal) μ).toReal = ‖S‖ := by
    calc
      (eLpNorm (fun ξ : ℕ → ℝ => S ξ) (2 : ENNReal) μ).toReal =
          ‖MemLp.toLp (fun ξ : ℕ → ℝ => S ξ) hS_mem‖ := (Lp.norm_toLp _ _).symm
      _ = ‖S‖ := by rw [hS_toLp]
  calc
    (eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal)
      (gaussianWeakDualMeasure J v)).toReal =
        (eLpNorm ((fun ω : WeakDual ℝ E => ω f) ∘ F) (2 : ENNReal) μ).toReal :=
          congrArg ENNReal.toReal hcomp.symm
    _ = (eLpNorm (fun ξ : ℕ → ℝ => S ξ) (2 : ENNReal) μ).toReal := by
      change (eLpNorm (fun ξ => F ξ f) (2 : ENNReal) μ).toReal = _
      rw [eLpNorm_congr_ae hae]
    _ = ‖S‖ := hSnorm
    _ ≤ (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
        (‖J f‖ * ∑' n, ‖v n‖) := by
          simpa [S, c] using gaussianSeriesConfiguration_eval_L2_norm_bound J v hv f

end Pphi2Clean.Continuum
