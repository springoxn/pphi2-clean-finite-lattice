import AImathPPhi2Clean.ProductGaussian
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

noncomputable section
namespace Pphi2Clean.GaussianField
open MeasureTheory ProbabilityTheory

def gaussianNoiseMeasure (σ : NNReal) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 σ)

instance gaussianNoiseMeasure_isProbability (σ : NNReal) :
    IsProbabilityMeasure (gaussianNoiseMeasure σ) := by
  unfold gaussianNoiseMeasure
  infer_instance

theorem gaussianNoiseMeasure_coordinate_map (σ : NNReal) (n : ℕ) :
    (gaussianNoiseMeasure σ).map (Function.eval n) = gaussianReal 0 σ := by
  unfold gaussianNoiseMeasure
  exact measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 σ) n |>.map_eq

theorem gaussianNoiseMeasure_coordinate_second_moment
    (σ : NNReal) (n : ℕ) :
    ∫ ξ : ℕ → ℝ, ξ n ^ 2 ∂gaussianNoiseMeasure σ = (σ : ℝ) := by
  calc
    ∫ ξ : ℕ → ℝ, ξ n ^ 2 ∂gaussianNoiseMeasure σ =
        ∫ y : ℝ, y ^ 2 ∂(gaussianNoiseMeasure σ).map (Function.eval n) := by
          exact (integral_map (μ := gaussianNoiseMeasure σ)
            (φ := Function.eval n) (measurable_pi_apply n).aemeasurable
            (f := fun y : ℝ => y ^ 2) (by fun_prop)).symm
    _ = ∫ y : ℝ, y ^ 2 ∂gaussianReal 0 σ := by
          rw [gaussianNoiseMeasure_coordinate_map]
    _ = (σ : ℝ) := Pphi2Clean.LatticeGaussian.gaussianReal_integral_sq_zero σ

theorem gaussianNoiseMeasure_coordinate_memLp (σ : NNReal) (p : NNReal) (n : ℕ) :
    MemLp (fun ξ : ℕ → ℝ => ξ n) p (gaussianNoiseMeasure σ) := by
  have hmap : Measure.map (Function.eval n) (gaussianNoiseMeasure σ) =
      gaussianReal 0 σ := gaussianNoiseMeasure_coordinate_map σ n
  have hmem : MemLp id p (Measure.map (Function.eval n)
      (gaussianNoiseMeasure σ)) := by
    rw [hmap]
    exact memLp_id_gaussianReal p
  simpa [Function.comp_def] using
    (memLp_map_measure_iff (f := Function.eval n)
      (μ := gaussianNoiseMeasure σ) (g := id) (by fun_prop)
      (measurable_pi_apply n).aemeasurable).1 hmem

theorem gaussianNoiseMeasure_coordinate_memLp_two (n : ℕ) :
    MemLp (fun ξ : ℕ → ℝ => ξ n) 2 (gaussianNoiseMeasure 1) :=
  gaussianNoiseMeasure_coordinate_memLp 1 2 n

theorem gaussianNoiseMeasure_coordinate_integral_zero (σ : NNReal) (n : ℕ) :
    ∫ ξ : ℕ → ℝ, ξ n ∂gaussianNoiseMeasure σ = 0 := by
  calc
    ∫ ξ : ℕ → ℝ, ξ n ∂gaussianNoiseMeasure σ =
        ∫ x : ℝ, x ∂(gaussianNoiseMeasure σ).map (Function.eval n) := by
          exact (integral_map (μ := gaussianNoiseMeasure σ)
            (φ := Function.eval n) (measurable_pi_apply n).aemeasurable
            (f := fun x : ℝ => x) (by fun_prop)).symm
    _ = ∫ x : ℝ, x ∂gaussianReal 0 σ := by
          rw [gaussianNoiseMeasure_coordinate_map]
    _ = 0 := integral_id_gaussianReal

theorem gaussianNoiseMeasure_coordinate_independent (σ : NNReal) :
    iIndepFun (fun n (ξ : ℕ → ℝ) => ξ n) (gaussianNoiseMeasure σ) := by
  unfold gaussianNoiseMeasure
  exact iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 σ)
    (X := fun _ y => y) (by fun_prop)

theorem gaussianNoiseMeasure_coordinate_cross_moment_zero
    (σ : NNReal) (n m : ℕ) (hnm : n ≠ m) :
    ∫ ξ : ℕ → ℝ, ξ n * ξ m ∂gaussianNoiseMeasure σ = 0 := by
  have hindep := (gaussianNoiseMeasure_coordinate_independent σ).indepFun hnm
  have hleft : AEStronglyMeasurable (fun ξ : ℕ → ℝ => ξ n)
      (gaussianNoiseMeasure σ) := (measurable_pi_apply n).aestronglyMeasurable
  have hright : AEStronglyMeasurable (fun ξ : ℕ → ℝ => ξ m)
      (gaussianNoiseMeasure σ) := (measurable_pi_apply m).aestronglyMeasurable
  calc
    ∫ ξ : ℕ → ℝ, ξ n * ξ m ∂gaussianNoiseMeasure σ =
        (∫ ξ : ℕ → ℝ, ξ n ∂gaussianNoiseMeasure σ) *
          (∫ ξ : ℕ → ℝ, ξ m ∂gaussianNoiseMeasure σ) := by
            simpa only [Pi.mul_apply] using
              hindep.integral_mul_eq_mul_integral hleft hright
    _ = 0 := by
      rw [gaussianNoiseMeasure_coordinate_integral_zero σ,
        gaussianNoiseMeasure_coordinate_integral_zero]
      ring

theorem gaussianNoiseMeasure_coordinate_variance (n : ℕ) :
    variance (fun ξ : ℕ → ℝ => ξ n) (gaussianNoiseMeasure 1) = 1 := by
  rw [variance_eq_integral (X := fun ξ : ℕ → ℝ => ξ n)
    (μ := gaussianNoiseMeasure 1) (measurable_pi_apply n).aemeasurable]
  rw [gaussianNoiseMeasure_coordinate_integral_zero]
  simpa [sub_zero] using gaussianNoiseMeasure_coordinate_second_moment 1 n

theorem gaussianNoiseMeasure_coordinate_variance_scaled (σ : NNReal) (n : ℕ) :
    variance (fun ξ : ℕ → ℝ => ξ n) (gaussianNoiseMeasure σ) = (σ : ℝ) := by
  rw [variance_eq_integral (X := fun ξ : ℕ → ℝ => ξ n)
    (μ := gaussianNoiseMeasure σ) (measurable_pi_apply n).aemeasurable]
  rw [gaussianNoiseMeasure_coordinate_integral_zero]
  simpa [sub_zero] using gaussianNoiseMeasure_coordinate_second_moment σ n

theorem gaussianNoiseMeasure_finsum_integral_zero (σ : NNReal) (s : Finset ℕ) (c : ℕ → ℝ) :
    ∫ ξ : ℕ → ℝ, (∑ n ∈ s, c n * ξ n) ∂gaussianNoiseMeasure σ = 0 := by
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
    simp_rw [gaussianNoiseMeasure_coordinate_integral_zero, mul_zero]
    simp
  · intro n hn
    exact (gaussianNoiseMeasure_coordinate_memLp σ 2 n).const_mul (c n) |>.integrable (by norm_num)

theorem gaussianNoiseMeasure_finsum_variance (σ : NNReal) (s : Finset ℕ) (c : ℕ → ℝ) :
    variance (fun ξ : ℕ → ℝ => ∑ n ∈ s, c n * ξ n)
      (gaussianNoiseMeasure σ) = (σ : ℝ) * ∑ n ∈ s, c n ^ 2 := by
  let X : ℕ → (ℕ → ℝ) → ℝ := fun n ξ => c n * ξ n
  have hI : iIndepFun (fun n ξ => c n * ξ n) (gaussianNoiseMeasure σ) := by
    convert (gaussianNoiseMeasure_coordinate_independent σ).comp
      (fun n y => c n * y) (fun _ => by fun_prop) using 1 <;>
      funext n ξ <;> rfl
  have hmem : ∀ n ∈ s, MemLp (X n) 2 (gaussianNoiseMeasure σ) := by
    intro n hn
    exact (gaussianNoiseMeasure_coordinate_memLp σ 2 n).const_mul (c n)
  have hindep : Set.Pairwise (↑s : Set ℕ)
      (fun n m => X n ⟂ᵢ[gaussianNoiseMeasure σ] X m) := by
    intro n hn m hm hnm
    exact (hI.indepFun hnm)
  calc
    variance (fun ξ : ℕ → ℝ => ∑ n ∈ s, X n ξ)
        (gaussianNoiseMeasure σ) =
        ∑ n ∈ s, variance (X n) (gaussianNoiseMeasure σ) := by
          have hsum : (fun ξ : ℕ → ℝ => ∑ n ∈ s, X n ξ) =
              ∑ n ∈ s, X n := by
            classical
            funext ξ
            simp only [Finset.sum_apply]
          rw [hsum]
          exact ProbabilityTheory.IndepFun.variance_sum hmem hindep
    _ = (σ : ℝ) * ∑ n ∈ s, c n ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [X, ProbabilityTheory.variance_const_mul]
      rw [gaussianNoiseMeasure_coordinate_variance_scaled σ]
      ring

theorem gaussianNoiseMeasure_finsum_variance_one (s : Finset ℕ) (c : ℕ → ℝ) :
    variance (fun ξ : ℕ → ℝ => ∑ n ∈ s, c n * ξ n)
      (gaussianNoiseMeasure 1) = ∑ n ∈ s, c n ^ 2 := by
  simpa using gaussianNoiseMeasure_finsum_variance 1 s c

theorem gaussianNoiseMeasure_finsum_second_moment (σ : NNReal) (s : Finset ℕ) (c : ℕ → ℝ) :
    ∫ ξ : ℕ → ℝ, (∑ n ∈ s, c n * ξ n) ^ 2 ∂gaussianNoiseMeasure σ =
      (σ : ℝ) * ∑ n ∈ s, c n ^ 2 := by
  rw [← gaussianNoiseMeasure_finsum_variance σ s c]
  rw [variance_eq_integral (X := fun ξ : ℕ → ℝ => ∑ n ∈ s, c n * ξ n)
    (μ := gaussianNoiseMeasure σ)
    ((by fun_prop : Measurable (fun ξ : ℕ → ℝ => ∑ n ∈ s, c n * ξ n)).aemeasurable)]
  simp [gaussianNoiseMeasure_finsum_integral_zero σ s c]

/-- If the scalar coordinate terms are summable in L², their pointwise series agrees
with the L² sum almost everywhere. The summability premise is explicit; this does not
claim that mere pointwise summability implies L² convergence. -/
theorem gaussianNoiseMeasure_series_L2_hasSum (c : ℕ → ℝ)
    (hc : (∑' n : ℕ, (eLpNorm (fun ξ : ℕ → ℝ => c n * ξ n) 2 (gaussianNoiseMeasure 1))) ≠ ⊤) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      HasSum (fun n => c n * ξ n)
        ((∑' n, (((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul (c n)).toLp
            (fun ξ : ℕ → ℝ => c n * ξ n))) ξ) := by
  let f : ℕ → Lp ℝ 2 (gaussianNoiseMeasure 1) := fun n =>
    ((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul (c n)).toLp
      (fun ξ : ℕ → ℝ => c n * ξ n)
  have hsum : ∑' n, ‖f n‖ₑ ≠ ⊤ := by
    simpa [f, Lp.enorm_toLp] using hc
  have hpoint := Lp.hasSum_coeFn_tsum hsum
  have hterms : ∀ᵐ ξ ∂gaussianNoiseMeasure 1, ∀ n, f n ξ = c n * ξ n :=
    ae_all_iff.mpr fun n =>
      (gaussianNoiseMeasure_coordinate_memLp_two n).const_mul (c n) |>.coeFn_toLp
  filter_upwards [hpoint, hterms] with ξ hξ hterms
  exact HasSum.congr_fun hξ fun n => (hterms n).symm

theorem gaussianNoiseMeasure_series_L2_hasSum_of_abs_summable (c : ℕ → ℝ)
    (hc : Summable (fun n => |c n|)) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      HasSum (fun n => c n * ξ n)
        ((∑' n, (((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul (c n)).toLp
            (fun ξ : ℕ → ℝ => c n * ξ n))) ξ) := by
  apply gaussianNoiseMeasure_series_L2_hasSum c
  let μ := gaussianNoiseMeasure 1
  let C : ENNReal := eLpNorm id (2 : ENNReal)
    (gaussianReal (0 : ℝ) 1)
  have hC : C ≠ ⊤ := ne_of_lt (memLp_id_gaussianReal' (2 : ENNReal) (by norm_num)).2
  have hcoord : ∀ n, eLpNorm (fun ξ : ℕ → ℝ => ξ n) (2 : ENNReal) μ = C := by
    intro n
    have hpres : MeasurePreserving (Function.eval n) μ (gaussianReal (0 : ℝ) 1) := by
      change MeasurePreserving (Function.eval n)
        (Measure.infinitePi (fun _ : ℕ => gaussianReal (0 : ℝ) 1))
        (gaussianReal (0 : ℝ) 1)
      exact measurePreserving_eval_infinitePi _ n
    have h := eLpNorm_comp_measurePreserving (g := fun x : ℝ => x)
      (p := (2 : ENNReal)) (μ := μ) (ν := gaussianReal (0 : ℝ) 1)
      measurable_id.aestronglyMeasurable hpres
    calc
      eLpNorm (fun ξ : ℕ → ℝ => ξ n) (2 : ENNReal) μ =
          eLpNorm (fun x : ℝ => x) (2 : ENNReal) (gaussianReal (0 : ℝ) 1) := h
      _ = C := rfl
  have hnorm : ∀ n, eLpNorm (fun ξ : ℕ → ℝ => c n * ξ n) (2 : ENNReal) μ =
      (‖c n‖₊ : ENNReal) * C := by
    intro n
    rw [show (fun ξ : ℕ → ℝ => c n * ξ n) = c n • fun ξ => ξ n by
      funext ξ
      simp]
    rw [eLpNorm_const_smul, hcoord]
    simpa only [enorm_eq_nnnorm]
  have hc_nn : Summable (fun n => ‖c n‖₊) := by
    have h1 : (fun n => (‖c n‖₊ : ℝ)) = fun n => |c n| := by
      funext n
      exact coe_nnnorm (c n)
    exact NNReal.summable_coe.mp (h1 ▸ hc)
  have hc_top : (∑' n, (‖c n‖₊ : ENNReal)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hc_nn
  have htotal : (∑' n, eLpNorm (fun ξ : ℕ → ℝ => c n * ξ n)
      (2 : ENNReal) μ) = (∑' n, (‖c n‖₊ : ENNReal)) * C := by
    calc
      _ = ∑' n, (‖c n‖₊ : ENNReal) * C := tsum_congr fun n => hnorm n
      _ = _ := ENNReal.tsum_mul_right
  rw [htotal]
  exact ENNReal.mul_ne_top hc_top hC


theorem gaussianNoiseMeasure_series_L2_norm_le_of_abs_summable (c : ℕ → ℝ)
    (hc : Summable (fun n => |c n|)) :
    ‖∑' n, (((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul (c n)).toLp
        (fun ξ : ℕ → ℝ => c n * ξ n))‖ ≤
      (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
        ∑' n, |c n| := by
  let μ := gaussianNoiseMeasure 1
  let C : ENNReal := eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)
  have hC : C ≠ ⊤ := ne_of_lt
    (memLp_id_gaussianReal' (2 : ENNReal) (by norm_num)).2
  have hcoord : ∀ n, eLpNorm (fun ξ : ℕ → ℝ => ξ n) (2 : ENNReal) μ = C := by
    intro n
    have hpres : MeasurePreserving (Function.eval n) μ (gaussianReal (0 : ℝ) 1) := by
      change MeasurePreserving (Function.eval n)
        (Measure.infinitePi (fun _ : ℕ => gaussianReal (0 : ℝ) 1))
        (gaussianReal (0 : ℝ) 1)
      exact measurePreserving_eval_infinitePi _ n
    have h := eLpNorm_comp_measurePreserving (g := fun x : ℝ => x)
      (p := (2 : ENNReal)) (μ := μ) (ν := gaussianReal (0 : ℝ) 1)
      measurable_id.aestronglyMeasurable hpres
    calc
      eLpNorm (fun ξ : ℕ → ℝ => ξ n) (2 : ENNReal) μ =
          eLpNorm (fun x : ℝ => x) (2 : ENNReal) (gaussianReal (0 : ℝ) 1) := h
      _ = C := rfl
  let g : ℕ → Lp ℝ 2 μ := fun n =>
    ((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul (c n)).toLp
      (fun ξ : ℕ → ℝ => c n * ξ n)
  have hnorm : ∀ n, ‖g n‖ ≤ C.toReal * |c n| := by
    intro n
    change ‖((gaussianNoiseMeasure_coordinate_memLp_two n).const_mul (c n)).toLp
      (fun ξ : ℕ → ℝ => c n * ξ n)‖ ≤ _
    rw [Lp.norm_toLp]
    rw [show (fun ξ : ℕ → ℝ => c n * ξ n) = c n • (fun ξ => ξ n) by
      funext ξ
      simp]
    rw [eLpNorm_const_smul, hcoord]
    simpa [C, ENNReal.toReal_mul, enorm_eq_nnnorm, Real.norm_eq_abs] using
      (le_of_eq (by ring : |c n| * C.toReal = C.toReal * |c n|))
  have hmajor : Summable (fun n => C.toReal * |c n|) := hc.mul_left C.toReal
  have hg : Summable g := Summable.of_norm_bounded hmajor hnorm
  have hgnorm : Summable (fun n => ‖g n‖) :=
    Summable.of_norm_bounded hmajor fun n => by simpa using hnorm n
  calc
    ‖∑' n, g n‖ ≤ ∑' n, ‖g n‖ := norm_tsum_le_tsum_norm hgnorm
    _ ≤ ∑' n, C.toReal * |c n| :=
      hgnorm.tsum_le_tsum hnorm hmajor
    _ = C.toReal * ∑' n, |c n| := tsum_mul_left

set_option maxHeartbeats 1600000 in
/-- Absolutely summable scalar coefficients produce an almost surely absolutely
summable Gaussian series under the countable iid standard Gaussian noise. -/
theorem gaussianNoiseMeasure_series_summable_ae (c : ℕ → ℝ)
    (hc : Summable (fun n => |c n|)) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      Summable (fun n => ξ n * c n) := by
  let μ := fun _ : ℕ => gaussianReal (0 : ℝ) 1
  let P := Measure.infinitePi μ
  let C := ∫⁻ x : ℝ, ↑‖x‖₊ ∂μ 0
  have hC : C ≠ ⊤ := by
    have h := (IsGaussian.integrable_dual (μ 0)
      (ContinuousLinearMap.id ℝ ℝ)).hasFiniteIntegral
    rw [hasFiniteIntegral_def] at h
    simp only [ContinuousLinearMap.id_apply, enorm_eq_nnnorm] at h
    exact h.ne
  have hc_nn : Summable (fun n => ‖c n‖₊) := by
    have h1 : (fun n => (‖c n‖₊ : ℝ)) = fun n => |c n| := by
      funext n; exact coe_nnnorm (c n)
    exact NNReal.summable_coe.mp (h1 ▸ hc)
  have hc_enn : tsum (fun n => ((‖c n‖₊ : NNReal) : ENNReal)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hc_nn
  have hmeasF : ∀ n, Measurable (fun ξ : ℕ → ℝ => (‖ξ n‖₊ : ENNReal)) :=
    fun n => (measurable_pi_apply n).nnnorm.coe_nnreal_ennreal
  have hmeas : ∀ n, Measurable
      (fun ξ : ℕ → ℝ => (‖ξ n‖₊ : ENNReal) * ‖c n‖₊) :=
    fun n => (hmeasF n).mul_const _
  have heval : ∀ n, ∫⁻ ξ, (‖ξ n‖₊ : ENNReal) ∂P = C := fun n =>
    (measurePreserving_eval_infinitePi μ n).lintegral_comp
      measurable_nnnorm.coe_nnreal_ennreal
  have hfinite : ∫⁻ ξ, ∑' n, ((‖ξ n‖₊ : ENNReal) * ‖c n‖₊) ∂P ≠ ⊤ := by
    rw [lintegral_tsum (fun n => (hmeas n).aemeasurable)]
    simp_rw [lintegral_mul_const _ (hmeasF _), heval, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hC hc_enn
  have hae := ae_lt_top (Measurable.ennreal_tsum hmeas) hfinite
  have hP : P = gaussianNoiseMeasure 1 := rfl
  rw [← hP]
  exact hae.mono fun ξ hξ => by
    simp_rw [← ENNReal.coe_mul] at hξ
    have hs : Summable (fun n => ‖ξ n‖₊ * ‖c n‖₊) :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp hξ.ne
    have hs' : Summable (fun n => ‖ξ n * c n‖) := by
      refine (NNReal.summable_coe.mpr hs).congr fun n => ?_
      rw [NNReal.coe_mul, coe_nnnorm, coe_nnnorm, norm_mul]
    exact hs'.of_norm


set_option maxHeartbeats 1600000 in
/-- Summable Hilbert coefficients yield an almost surely convergent Gaussian
series in every complete real Hilbert space. -/
theorem gaussianNoiseMeasure_hilbert_series_summable_ae
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (v : ℕ → K) (hv : Summable (fun n => ‖v n‖)) :
    ∀ᵐ ξ ∂gaussianNoiseMeasure 1,
      Summable (fun n => ξ n • v n) := by
  let μ := fun _ : ℕ => gaussianReal (0 : ℝ) 1
  let P := Measure.infinitePi μ
  let C := ∫⁻ x : ℝ, ↑‖x‖₊ ∂μ 0
  have hC : C ≠ ⊤ := by
    have h := (IsGaussian.integrable_dual (μ 0)
      (ContinuousLinearMap.id ℝ ℝ)).hasFiniteIntegral
    rw [hasFiniteIntegral_def] at h
    simp only [ContinuousLinearMap.id_apply, enorm_eq_nnnorm] at h
    exact h.ne
  have hv_nn : Summable (fun n => ‖v n‖₊) := by
    have h1 : (fun n => (‖v n‖₊ : ℝ)) = fun n => ‖v n‖ := by
      funext n; exact coe_nnnorm (v n)
    exact NNReal.summable_coe.mp (h1 ▸ hv)
  have hv_enn : tsum (fun n => ((‖v n‖₊ : NNReal) : ENNReal)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hv_nn
  have hmeasF : ∀ n, Measurable (fun ξ : ℕ → ℝ => (‖ξ n‖₊ : ENNReal)) :=
    fun n => (measurable_pi_apply n).nnnorm.coe_nnreal_ennreal
  have hmeas : ∀ n, Measurable
      (fun ξ : ℕ → ℝ => (‖ξ n‖₊ : ENNReal) * ‖v n‖₊) :=
    fun n => (hmeasF n).mul_const _
  have heval : ∀ n, ∫⁻ ξ, (‖ξ n‖₊ : ENNReal) ∂P = C := fun n =>
    (measurePreserving_eval_infinitePi μ n).lintegral_comp
      measurable_nnnorm.coe_nnreal_ennreal
  have hfinite : ∫⁻ ξ, ∑' n, ((‖ξ n‖₊ : ENNReal) * ‖v n‖₊) ∂P ≠ ⊤ := by
    rw [lintegral_tsum (fun n => (hmeas n).aemeasurable)]
    simp_rw [lintegral_mul_const _ (hmeasF _), heval, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hC hv_enn
  have hae := ae_lt_top (Measurable.ennreal_tsum hmeas) hfinite
  have hP : P = gaussianNoiseMeasure 1 := rfl
  rw [← hP]
  exact hae.mono fun ξ hξ => by
    simp_rw [← ENNReal.coe_mul] at hξ
    have hs : Summable (fun n => ‖ξ n‖₊ * ‖v n‖₊) :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp hξ.ne
    have hs' : Summable (fun n => ‖ξ n • v n‖) := by
      refine (NNReal.summable_coe.mpr hs).congr fun n => ?_
      rw [NNReal.coe_mul, coe_nnnorm, coe_nnnorm, norm_smul]
    exact hs'.of_norm
end Pphi2Clean.GaussianField
