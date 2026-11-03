import AImathPPhi2Clean.PhysicalLatticeSampling
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Order.Filter.Tendsto

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice Complex

private def gaussianLinearCLM {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (f : ι → ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card ι)) →L[ℝ] ℝ :=
  innerSL ℝ (WithLp.toLp 2
    (fun k : Fin (Fintype.card ι) => (T f) ((Fintype.equivFin ι).symm k)))

private theorem covarianceConfiguration_eq_gaussianLinear {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (f : ι → ℝ)
    (z : Fin (Fintype.card ι) → ℝ) :
    covarianceConfiguration T z f =
      gaussianLinearCLM T f (WithLp.toLp 2 z) := by
  simp [gaussianLinearCLM, covarianceConfiguration_apply, innerSL_apply_apply,
    PiLp.inner_apply]

/-- The actual finite Gaussian configuration has a Gaussian law in every
linear test observable. This is the distributional step, not just a moment claim. -/
theorem covarianceConfiguration_hasGaussianLaw {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (f : ι → ℝ) :
    HasGaussianLaw (fun z => covarianceConfiguration T z f)
      (Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1) := by
  let μ := Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1
  let E := EuclideanSpace ℝ (Fin (Fintype.card ι))
  let L := gaussianLinearCLM T f
  have hstd : (μ.map (WithLp.toLp 2)) = stdGaussian E := by
    simpa [μ, E, Pphi2Clean.LatticeGaussian.productGaussian] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin (Fintype.card ι)))
  have hmap : μ.map (fun z => covarianceConfiguration T z f) =
      (stdGaussian E).map L := by
    rw [show (fun z => covarianceConfiguration T z f) =
        (fun z => L (WithLp.toLp 2 z)) from by
          funext z
          exact covarianceConfiguration_eq_gaussianLinear T f z]
    rw [show (fun z => L (WithLp.toLp 2 z)) =
      (L ∘ WithLp.toLp 2) from rfl]
    rw [← Measure.map_map (g := L) (f := WithLp.toLp 2) (by fun_prop) (by fun_prop), hstd]
  have hId : HasGaussianLaw id (stdGaussian E) := by
    exact IsGaussian.hasGaussianLaw_id
  have hlin : HasGaussianLaw (fun v : E => L v) (stdGaussian E) :=
    hId.map_of_measurable L (by fun_prop)
  have hG : IsGaussian (μ.map (fun z => covarianceConfiguration T z f)) := by
    rw [hmap]
    exact hlin.isGaussian_map
  have hproj : Measurable (fun ω : WeakDual ℝ (ι → ℝ) => ω f) :=
    (measurable_pi_apply f).comp (comap_measurable _)
  have hXmeas : Measurable (fun z => covarianceConfiguration T z f) :=
    hproj.comp (covarianceConfiguration_measurable T)
  exact hG.hasGaussianLaw

/-- The finite Gaussian configuration is centered in every test direction. -/
theorem covarianceConfiguration_mean_zero {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (f : ι → ℝ) :
    ∫ z, covarianceConfiguration T z f ∂
      Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1 = 0 := by
  let μ := Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1
  let E := EuclideanSpace ℝ (Fin (Fintype.card ι))
  let L := gaussianLinearCLM T f
  have hstd : (μ.map (WithLp.toLp 2)) = stdGaussian E := by
    simpa [μ, E, Pphi2Clean.LatticeGaussian.productGaussian] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin (Fintype.card ι)))
  have hmap : μ.map (fun z => covarianceConfiguration T z f) =
      (stdGaussian E).map L := by
    rw [show (fun z => covarianceConfiguration T z f) =
        (fun z => L (WithLp.toLp 2 z)) from by
          funext z
          exact covarianceConfiguration_eq_gaussianLinear T f z]
    rw [show (fun z => L (WithLp.toLp 2 z)) =
      (L ∘ WithLp.toLp 2) from rfl]
    rw [← Measure.map_map (g := L) (f := WithLp.toLp 2) (by fun_prop) (by fun_prop), hstd]
  have hcoord (k : Fin (Fintype.card ι)) :
      ∫ z : Fin (Fintype.card ι) → ℝ, z k ∂
        Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1 = 0 := by
    have h := integral_map (μ := Pphi2Clean.LatticeGaussian.productGaussian
      (Fintype.card ι) 1) (measurable_pi_apply k).aemeasurable
      (f := fun y : ℝ => y) (by fun_prop)
    rw [Pphi2Clean.LatticeGaussian.productGaussian_coordinate_map] at h
    calc
      _ = ∫ y : ℝ, y ∂gaussianReal 0 1 := h.symm
      _ = 0 := integral_id_gaussianReal
  simp_rw [covarianceConfiguration_apply]
  rw [integral_finsetSum]
  · simp_rw [integral_mul_const, hcoord]
    simp
  · intro k hk
    exact (((memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) k)).mul_const _).integrable (by norm_num)

/-- Exact characteristic function of each linear test observable. -/
theorem covarianceConfiguration_charFun {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (f : ι → ℝ) (t : ℝ) :
    charFun ((Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1).map
      (fun z => covarianceConfiguration T z f)) t =
      Complex.exp (-(t ^ 2) * ‖T f‖ ^ 2 / 2) := by
  rw [(covarianceConfiguration_hasGaussianLaw T f).map_eq_gaussianReal,
    charFun_gaussianReal]
  have hm := covarianceConfiguration_mean_zero T f
  have hXmeas : Measurable (fun z => covarianceConfiguration T z f) :=
    ((measurable_pi_apply f).comp (comap_measurable _)).comp
      (covarianceConfiguration_measurable T)
  rw [hm]
  have hvar : Var[fun z => covarianceConfiguration T z f;
      Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1] =
      @inner ℝ (EuclideanSpace ℝ ι) _ (T f) (T f) := by
    rw [variance_eq_integral hXmeas.aemeasurable, hm]
    simp only [sub_zero]
    exact covarianceConfiguration_second_moment T f
  have hinner := real_inner_self_eq_norm_sq (T f)
  rw [hinner] at hvar
  have hnonneg : 0 ≤ ‖T f‖ ^ 2 := sq_nonneg _
  rw [hvar, Real.toNNReal_of_nonneg hnonneg]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  congr 1
  push_cast
  ring

theorem latticeGJConfiguration_charFun (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeSites d N → ℝ) (t : ℝ) :
    charFun ((Pphi2Clean.LatticeGaussian.productGaussian
      (Fintype.card (FinLatticeSites d N)) 1).map
        (fun z => covarianceConfiguration
          (latticeCovarianceGJ d N a mass ha hmass) z f)) t =
      Complex.exp (-(t ^ 2) * ‖latticeCovarianceGJ d N a mass ha hmass f‖ ^ 2 / 2) :=
  covarianceConfiguration_charFun
    (latticeCovarianceGJ d N a mass ha hmass) f t

theorem latticeGJConfiguration_mean_zero (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeSites d N → ℝ) :
    ∫ z, covarianceConfiguration (latticeCovarianceGJ d N a mass ha hmass) z f ∂
      Pphi2Clean.LatticeGaussian.productGaussian
        (Fintype.card (FinLatticeSites d N)) 1 = 0 :=
  covarianceConfiguration_mean_zero (latticeCovarianceGJ d N a mass ha hmass) f

theorem finiteCovarianceGaussianMeasure_eval_map_eq {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (f : ι → ℝ) :
    (finiteCovarianceGaussianMeasure T).map
      (fun ω : WeakDual ℝ (ι → ℝ) => ω f) =
      (Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1).map
        (fun z => covarianceConfiguration T z f) := by
  unfold finiteCovarianceGaussianMeasure
  exact Measure.map_map
    ((measurable_pi_apply f).comp (comap_measurable _))
    (covarianceConfiguration_measurable T)

theorem finiteCovarianceGaussianMeasure_eval_mean_zero {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (f : ι → ℝ) :
    ∫ ω : WeakDual ℝ (ι → ℝ), ω f ∂finiteCovarianceGaussianMeasure T = 0 := by
  have heval : Measurable (fun ω : WeakDual ℝ (ι → ℝ) => ω f) :=
    (measurable_pi_apply f).comp (comap_measurable _)
  rw [finiteCovarianceGaussianMeasure,
    integral_map (covarianceConfiguration_measurable T).aemeasurable heval.aestronglyMeasurable]
  exact covarianceConfiguration_mean_zero T f

theorem physicalGJMeasure_eval_map_eq (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    (physicalGJMeasure d N a mass ha hmass).map
      (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f) =
      (finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ d N a mass ha hmass)).map
        (fun ω : WeakDual ℝ (Fin (Fintype.card (FinLatticeSites d N)) → ℝ) =>
          ω (latticeTestField (physicalTestEval d N a) f)) := by
  have heval : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f) :=
    (measurable_pi_apply f).comp (comap_measurable _)
  calc
    _ = (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ d N a mass ha hmass)).map
          ((fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f) ∘
            latticeEmbedLift (physicalTestEval d N a)) :=
      Measure.map_map heval (latticeEmbedLift_measurable (physicalTestEval d N a))
    _ = (finiteCovarianceGaussianMeasure
        (numberedLatticeCovarianceGJ d N a mass ha hmass)).map
          (fun ω => ω (latticeTestField (physicalTestEval d N a) f)) := by
      congr 1
      funext ω
      exact latticeEmbedLift_eval_eq (physicalTestEval d N a) ω f

theorem finiteCovarianceGaussianMeasure_eval_hasGaussianLaw {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (f : ι → ℝ) :
    HasGaussianLaw (fun ω : WeakDual ℝ (ι → ℝ) => ω f)
      (finiteCovarianceGaussianMeasure T) := by
  have heval : Measurable (fun ω : WeakDual ℝ (ι → ℝ) => ω f) :=
    (measurable_pi_apply f).comp (comap_measurable _)
  have hmap := finiteCovarianceGaussianMeasure_eval_map_eq T f
  have hG : IsGaussian ((finiteCovarianceGaussianMeasure T).map
      (fun ω : WeakDual ℝ (ι → ℝ) => ω f)) := by
    rw [hmap]
    exact (covarianceConfiguration_hasGaussianLaw T f).isGaussian_map
  exact hG.hasGaussianLaw

theorem physicalGJMeasure_eval_mean_zero (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ), ω f ∂
      physicalGJMeasure d N a mass ha hmass = 0 := by
  let eval := physicalTestEval d N a
  have heval : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f) :=
    (measurable_pi_apply f).comp (comap_measurable _)
  rw [physicalGJMeasure, integral_map (latticeEmbedLift_measurable eval).aemeasurable
    heval.aestronglyMeasurable]
  calc
    _ = ∫ ω : WeakDual ℝ (Fin (Fintype.card (FinLatticeSites d N)) → ℝ),
          ω (latticeTestField eval f) ∂
            finiteCovarianceGaussianMeasure
              (numberedLatticeCovarianceGJ d N a mass ha hmass) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact latticeEmbedLift_eval_eq eval ω f
    _ = 0 := finiteCovarianceGaussianMeasure_eval_mean_zero
      (numberedLatticeCovarianceGJ d N a mass ha hmass) (latticeTestField eval f)

theorem physicalGJMeasure_charFun (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (t : ℝ) :
    charFun ((physicalGJMeasure d N a mass ha hmass).map
      (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f)) t =
      Complex.exp (-(t ^ 2) *
        ‖numberedLatticeCovarianceGJ d N a mass ha hmass
          (latticeTestField (physicalTestEval d N a) f)‖ ^ 2 / 2) := by
  rw [physicalGJMeasure_eval_map_eq d N a mass ha hmass f,
    finiteCovarianceGaussianMeasure_eval_map_eq
      (numberedLatticeCovarianceGJ d N a mass ha hmass)
      (latticeTestField (physicalTestEval d N a) f)]
  exact covarianceConfiguration_charFun
    (numberedLatticeCovarianceGJ d N a mass ha hmass)
    (latticeTestField (physicalTestEval d N a) f) t

theorem physicalGJMeasure_eval_hasGaussianLaw (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    HasGaussianLaw (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f)
      (physicalGJMeasure d N a mass ha hmass) := by
  let eval := physicalTestEval d N a
  let T := numberedLatticeCovarianceGJ d N a mass ha hmass
  have heval : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f) :=
    (measurable_pi_apply f).comp (comap_measurable _)
  have hpush := physicalGJMeasure_eval_map_eq d N a mass ha hmass f
  have hG : IsGaussian ((physicalGJMeasure d N a mass ha hmass).map
      (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f)) := by
    rw [hpush]
    exact (finiteCovarianceGaussianMeasure_eval_hasGaussianLaw T
      (latticeTestField eval f)).isGaussian_map
  exact hG.hasGaussianLaw
private def covarianceConfigurationFamilyCLM {ι : Type*} [Fintype ι] {m : ℕ}
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (fs : Fin m → ι → ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card ι)) →L[ℝ] EuclideanSpace ℝ (Fin m) := by
  let L : EuclideanSpace ℝ (Fin (Fintype.card ι)) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap.comp
      (ContinuousLinearMap.pi (fun j => gaussianLinearCLM T (fs j))).toLinearMap
  exact { L with cont := L.continuous_of_finiteDimensional }

theorem covarianceConfiguration_family_hasGaussianLaw {ι : Type*} [Fintype ι] {m : ℕ}
    (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (fs : Fin m → ι → ℝ) :
    HasGaussianLaw
      (fun z => WithLp.toLp 2 (fun j => covarianceConfiguration T z (fs j)))
      (Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1) := by
  let μ := Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1
  let E := EuclideanSpace ℝ (Fin (Fintype.card ι))
  let L := covarianceConfigurationFamilyCLM T fs
  have hstd : μ.map (WithLp.toLp 2) = stdGaussian E := by
    simpa [μ, E, Pphi2Clean.LatticeGaussian.productGaussian] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin (Fintype.card ι)))
  have hfun : (fun z => WithLp.toLp 2 (fun j => covarianceConfiguration T z (fs j))) =
      fun z => L (WithLp.toLp 2 z) := by
    funext z
    ext j
    simpa [L, covarianceConfigurationFamilyCLM] using
      covarianceConfiguration_eq_gaussianLinear T (fs j) z
  have hmap : μ.map (fun z => WithLp.toLp 2
      (fun j => covarianceConfiguration T z (fs j))) = (stdGaussian E).map L := by
    rw [hfun, show (fun z => L (WithLp.toLp 2 z)) = (L ∘ WithLp.toLp 2) from rfl]
    rw [← Measure.map_map (g := L) (f := WithLp.toLp 2) (by fun_prop) (by fun_prop), hstd]
  have hId : HasGaussianLaw id (stdGaussian E) := IsGaussian.hasGaussianLaw_id
  have hL : HasGaussianLaw (fun v : E => L v) (stdGaussian E) :=
    hId.map_of_measurable L (by fun_prop)
  have hG : IsGaussian (μ.map (fun z => WithLp.toLp 2
      (fun j => covarianceConfiguration T z (fs j)))) := by
    rw [hmap]
    exact hL.isGaussian_map
  have hmeas : Measurable (fun z => WithLp.toLp 2
      (fun j => covarianceConfiguration T z (fs j))) := by
    rw [hfun]
    fun_prop
  exact hG.hasGaussianLaw

theorem finiteCovarianceGaussianMeasure_family_hasGaussianLaw {ι : Type*} [Fintype ι]
    {m : ℕ} (T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) (fs : Fin m → ι → ℝ) :
    HasGaussianLaw
      (fun ω : WeakDual ℝ (ι → ℝ) => WithLp.toLp 2 (fun j => ω (fs j)))
      (finiteCovarianceGaussianMeasure T) := by
  have hvector : Measurable (fun ω : WeakDual ℝ (ι → ℝ) =>
      WithLp.toLp 2 (fun j => ω (fs j))) := by
    have hcoord : ∀ j, Measurable (fun ω : WeakDual ℝ (ι → ℝ) => ω (fs j)) := by
      intro j
      exact (measurable_pi_apply (fs j)).comp (comap_measurable _)
    have htoLp : Continuous (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) :=
      PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)
    exact htoLp.measurable.comp (measurable_pi_lambda _ hcoord)
  have hmap : (finiteCovarianceGaussianMeasure T).map
      (fun ω : WeakDual ℝ (ι → ℝ) => WithLp.toLp 2 (fun j => ω (fs j))) =
      (Pphi2Clean.LatticeGaussian.productGaussian (Fintype.card ι) 1).map
        (fun z => WithLp.toLp 2 (fun j => covarianceConfiguration T z (fs j))) := by
    unfold finiteCovarianceGaussianMeasure
    exact Measure.map_map hvector (covarianceConfiguration_measurable T)
  have hG : IsGaussian ((finiteCovarianceGaussianMeasure T).map
      (fun ω : WeakDual ℝ (ι → ℝ) => WithLp.toLp 2 (fun j => ω (fs j)))) := by
    rw [hmap]
    exact (covarianceConfiguration_family_hasGaussianLaw T fs).isGaussian_map
  exact hG.hasGaussianLaw

theorem physicalGJMeasure_family_hasGaussianLaw (d N : ℕ) [NeZero N]
    {m : ℕ} (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    HasGaussianLaw
      (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) =>
        WithLp.toLp 2 (fun j => ω (fs j)))
      (physicalGJMeasure d N a mass ha hmass) := by
  let eval := physicalTestEval d N a
  let T := numberedLatticeCovarianceGJ d N a mass ha hmass
  have hvector : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin d → ℝ) ℝ) =>
        WithLp.toLp 2 (fun j => ω (fs j))) := by
    have hcoord : ∀ j, Measurable (fun ω : WeakDual ℝ
        (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω (fs j)) := by
      intro j
      exact (measurable_pi_apply (fs j)).comp (comap_measurable _)
    have htoLp : Continuous (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) :=
      PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)
    exact htoLp.measurable.comp (measurable_pi_lambda _ hcoord)
  have hpush : (physicalGJMeasure d N a mass ha hmass).map
      (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) =>
        WithLp.toLp 2 (fun j => ω (fs j))) =
      (finiteCovarianceGaussianMeasure T).map
        (fun ω : WeakDual ℝ (Fin (Fintype.card (FinLatticeSites d N)) → ℝ) =>
          WithLp.toLp 2 (fun j => ω (latticeTestField eval (fs j)))) := by
    calc
      _ = (finiteCovarianceGaussianMeasure T).map
            ((fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) =>
              WithLp.toLp 2 (fun j => ω (fs j))) ∘ latticeEmbedLift eval) :=
        Measure.map_map hvector (latticeEmbedLift_measurable eval)
      _ = (finiteCovarianceGaussianMeasure T).map
            (fun ω => WithLp.toLp 2 (fun j => ω (latticeTestField eval (fs j)))) := by
        congr 1
        funext ω
        ext j
        exact latticeEmbedLift_eval_eq eval ω (fs j)
  have hG : IsGaussian ((physicalGJMeasure d N a mass ha hmass).map
      (fun ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) =>
        WithLp.toLp 2 (fun j => ω (fs j)))) := by
    rw [hpush]
    exact (finiteCovarianceGaussianMeasure_family_hasGaussianLaw T
      (fun j => latticeTestField eval (fs j))).isGaussian_map
  exact hG.hasGaussianLaw

theorem physicalGJMeasure_family_mean_zero (d N : ℕ) [NeZero N]
    {m : ℕ} (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∀ j, ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
      ω (fs j) ∂physicalGJMeasure d N a mass ha hmass = 0 := by
  intro j
  exact physicalGJMeasure_eval_mean_zero d N a mass ha hmass (fs j)


/-- Exact mixed covariance of the actual sampled GJ measure. The mean-zero
results above identify this mixed moment with covariance. -/
theorem physicalGJMeasure_mixedMoment (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
      ω f * ω g ∂physicalGJMeasure d N a mass ha hmass =
      @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
        (numberedLatticeCovarianceGJ d N a mass ha hmass
          (latticeTestField (physicalTestEval d N a) f))
        (numberedLatticeCovarianceGJ d N a mass ha hmass
          (latticeTestField (physicalTestEval d N a) g)) := by
  let eval := physicalTestEval d N a
  have hf : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f) :=
    (measurable_pi_apply f).comp (comap_measurable _)
  have hg : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω g) :=
    (measurable_pi_apply g).comp (comap_measurable _)
  have hprod : Measurable (fun ω : WeakDual ℝ
      (BoundedContinuousFunction (Fin d → ℝ) ℝ) => ω f * ω g) := hf.mul hg
  rw [physicalGJMeasure,
    integral_map (latticeEmbedLift_measurable eval).aemeasurable
      hprod.aestronglyMeasurable]
  simp_rw [latticeEmbedLift_eval_eq]
  exact finiteCovarianceGaussianMeasure_covariance
    (numberedLatticeCovarianceGJ d N a mass ha hmass)
    (latticeTestField eval f) (latticeTestField eval g)

/-- A source-side covariance limit transfers exactly to the covariance of the
actual sampled GJ measures.  The analytic resolvent-convergence hypothesis is
intentionally kept explicit; this theorem does not assert it. -/
theorem physicalGJMeasure_covariance_tendsto_of_inner_tendsto
    {ι : Type*} (l : Filter ι) (d : ℕ)
    (N : ι → ℕ) (hN : ∀ i, NeZero (N i))
    (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (mass : ℝ) (hmass : 0 < mass)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ →
      BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun i =>
        letI : NeZero (N i) := hN i
        @inner ℝ (EuclideanSpace ℝ
          (Fin (Fintype.card (FinLatticeSites d (N i))))) _
          (numberedLatticeCovarianceGJ d (N i) (a i) mass (ha i) hmass
            (latticeTestField (physicalTestEval d (N i) (a i)) f))
          (numberedLatticeCovarianceGJ d (N i) (a i) mass (ha i) hmass
            (latticeTestField (physicalTestEval d (N i) (a i)) g)))
      l (nhds (C f g))) :
    ∀ f g, Filter.Tendsto
      (fun i =>
        letI : NeZero (N i) := hN i
        ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          ω f * ω g ∂physicalGJMeasure d (N i) (a i) mass (ha i) hmass)
      l (nhds (C f g)) := by
  intro f g
  have hEq :
      (fun i =>
        letI : NeZero (N i) := hN i
        ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          ω f * ω g ∂physicalGJMeasure d (N i) (a i) mass (ha i) hmass) =
      (fun i =>
        letI : NeZero (N i) := hN i
        @inner ℝ (EuclideanSpace ℝ
          (Fin (Fintype.card (FinLatticeSites d (N i))))) _
          (numberedLatticeCovarianceGJ d (N i) (a i) mass (ha i) hmass
            (latticeTestField (physicalTestEval d (N i) (a i)) f))
          (numberedLatticeCovarianceGJ d (N i) (a i) mass (ha i) hmass
            (latticeTestField (physicalTestEval d (N i) (a i)) g))) := by
    funext i
    letI : NeZero (N i) := hN i
    exact physicalGJMeasure_mixedMoment d (N i) (a i) mass (ha i) hmass f g
  rw [hEq]
  exact hinner f g


/-- Fixed physical volume: `N = n + 1` and `a = L / N`. For the intended
flat-torus Green covariance `C(f,g) = ⟪f, (-Δ + mass^2)⁻¹ g⟫`, this theorem
transfers convergence of the explicit discrete covariance inner products to
convergence for the actual physical measures. It does not assume or prove the
finite-difference resolvent convergence itself. -/
theorem physicalGJMeasure_fixedVolume_covariance_tendsto_of_inner_tendsto
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ →
      BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (hinner : ∀ f g, Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        @inner ℝ (EuclideanSpace ℝ
          (Fin (Fintype.card (FinLatticeSites d N)))) _
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField
              (physicalTestEval d N (L / (N : ℝ))) f))
          (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
            (latticeTestField
              (physicalTestEval d N (L / (N : ℝ))) g)))
      Filter.atTop (nhds (C f g))) :
    ∀ f g, Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          ω f * ω g ∂physicalGJMeasure d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass)
      Filter.atTop (nhds (C f g)) := by
  have hN : ∀ n : ℕ, NeZero (n + 1) := fun n => ⟨Nat.succ_ne_zero n⟩
  have ha : ∀ n : ℕ, 0 < L / ((n + 1 : ℕ) : ℝ) := by
    intro n
    exact div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))
  exact physicalGJMeasure_covariance_tendsto_of_inner_tendsto
    Filter.atTop d (fun n : ℕ => n + 1) hN
    (fun n : ℕ => L / ((n + 1 : ℕ) : ℝ)) ha mass hmass C hinner

end Pphi2Clean.Continuum
