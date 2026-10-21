import AImathPPhi2Clean.GaussianConfiguration

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory

/-- A source-measure second-moment estimate survives a measurable lattice-to-continuum
embedding and its pushforward measure.  This is the interface consumed by concrete
`latticeCovarianceGJ`/`latticeEmbedLift` instances. -/
theorem pushforward_eval_L2_norm_le
    {Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (μ : Measure Ω) (ι : Ω → WeakDual ℝ E)
    (hι : Measurable ι) (f : E) (g : Ω → ℝ)
    (h_eval : ∀ᵐ ω ∂μ, ι ω f = g ω)
    (C : ℝ) (hC : (eLpNorm g (2 : ENNReal) μ).toReal ≤ C) :
    (eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal)
      (Measure.map ι μ)).toReal ≤ C := by
  have hEval : Measurable (fun ω : WeakDual ℝ E => ω f) := by
    change Measurable (fun ω : WeakDual ℝ E => (ω : E → ℝ) f)
    exact (measurable_pi_apply f).comp (comap_measurable _)
  have hpres : MeasurePreserving ι μ (Measure.map ι μ) :=
    ⟨hι, rfl⟩
  have hcomp : eLpNorm ((fun ω : WeakDual ℝ E => ω f) ∘ ι)
      (2 : ENNReal) μ =
      eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal) (Measure.map ι μ) :=
    eLpNorm_comp_measurePreserving hEval.aestronglyMeasurable hpres
  calc
    (eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal)
      (Measure.map ι μ)).toReal =
        (eLpNorm ((fun ω : WeakDual ℝ E => ω f) ∘ ι)
          (2 : ENNReal) μ).toReal := congrArg ENNReal.toReal hcomp.symm
    _ = (eLpNorm g (2 : ENNReal) μ).toReal := by
      rw [eLpNorm_congr_ae]
      exact h_eval
    _ ≤ C := hC


/-- A certificate bundle with an explicit uniform constant. -/
structure LatticeGaussianUniformData
    {ι Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] where
  latticeGaussianMeasure : ι → Measure Ω
  latticeEmbedLift : ι → Ω → WeakDual ℝ E
  lattice_eval : ι → E → Ω → ℝ
  bound : ℝ
  embed_measurable : ∀ i, Measurable (latticeEmbedLift i)
  embed_eval_ae : ∀ i f, ∀ᵐ ω ∂latticeGaussianMeasure i,
    latticeEmbedLift i ω f = lattice_eval i f ω
  source_L2_bound : ∀ i f,
    (eLpNorm (lattice_eval i f) (2 : ENNReal)
      (latticeGaussianMeasure i)).toReal ≤ bound


/-- A finite lattice field used by the concrete embedding layer.
This is only the algebraic finite-lattice source space; no continuum-limit
claim is attached to it. -/
abbrev FiniteLatticeField (n : ℕ) := Fin n → ℝ

abbrev FiniteLatticeConfiguration (n : ℕ) := WeakDual ℝ (FiniteLatticeField n)

/-- The finite lattice test field induced by a family of continuous evaluation
functionals on the continuum test space. -/
def latticeTestField
    {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    (eval : Fin n → E →L[ℝ] ℝ) (f : E) : FiniteLatticeField n :=
  fun x => eval x f

/-- Concrete finite-sum lattice-to-configuration lift.  The family `eval`
represents evaluation of a continuum test function at the physical lattice
sites, including any Riemann-sum weights. -/
def latticeEmbedLift
    {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    (eval : Fin n → E →L[ℝ] ℝ)
    (ω : FiniteLatticeConfiguration n) : WeakDual ℝ E :=
  (∑ x : Fin n, (ω (Pi.single x (1 : ℝ))) • eval x : E →L[ℝ] ℝ)

@[simp] theorem latticeEmbedLift_eval
    {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    (eval : Fin n → E →L[ℝ] ℝ)
    (ω : FiniteLatticeConfiguration n) (f : E) :
    latticeEmbedLift eval ω f =
      ∑ x : Fin n, ω (Pi.single x (1 : ℝ)) * eval x f := by
  unfold latticeEmbedLift
  change (∑ x : Fin n, (ω (Pi.single x (1 : ℝ))) • eval x) f = _
  rw [ContinuousLinearMap.sum_apply]
  simp [smul_eq_mul]

/-- The concrete finite lift is continuous, hence measurable, for the weak-dual
topology. -/
theorem latticeEmbedLift_continuous
    {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    (eval : Fin n → E →L[ℝ] ℝ) :
    Continuous (latticeEmbedLift eval) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  rw [show (fun a : FiniteLatticeConfiguration n => latticeEmbedLift eval a f) =
      (fun a => ∑ x : Fin n,
        a (Pi.single x (1 : ℝ) : FiniteLatticeField n) * eval x f) by
        funext a
        exact latticeEmbedLift_eval eval a f]
  exact continuous_finsetSum (Finset.univ : Finset (Fin n)) (fun x _ =>
    (WeakDual.eval_continuous
      (Pi.single x (1 : ℝ) : FiniteLatticeField n)).mul_const (eval x f))

/-- Measurability of the concrete lift in the cylindrical weak-dual sigma
algebra. -/
theorem latticeEmbedLift_measurable
    {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    (eval : Fin n → E →L[ℝ] ℝ) :
    Measurable (latticeEmbedLift eval) := by
  rw [measurable_iff_comap_le]
  show (MeasurableSpace.comap (fun ω f => ω f) MeasurableSpace.pi).comap
      (latticeEmbedLift eval) ≤ _
  rw [MeasurableSpace.comap_comp]
  apply (measurable_pi_lambda _ ?_).comap_le
  intro f
  change Measurable (fun ω : FiniteLatticeConfiguration n => latticeEmbedLift eval ω f)
  rw [show (fun ω : FiniteLatticeConfiguration n => latticeEmbedLift eval ω f) =
      (fun ω => ∑ x : Fin n,
        ω (Pi.single x (1 : ℝ) : FiniteLatticeField n) * eval x f) by
        funext ω; exact latticeEmbedLift_eval eval ω f]
  apply Finset.measurable_sum
  intro x hx
  have hcoord : Measurable
      (fun ω : FiniteLatticeConfiguration n =>
        ω (Pi.single x (1 : ℝ) : FiniteLatticeField n)) :=
    (measurable_pi_apply (Pi.single x (1 : ℝ) : FiniteLatticeField n)).comp
      (comap_measurable _)
  exact hcoord.mul_const (eval x f)

/-- The finite Pi-basis identity connecting the concrete lift to a source
configuration evaluation. -/
theorem latticeEmbedLift_eval_eq
    {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    (eval : Fin n → E →L[ℝ] ℝ)
    (ω : FiniteLatticeConfiguration n) (f : E) :
    latticeEmbedLift eval ω f = ω (latticeTestField eval f) := by
  rw [latticeEmbedLift_eval]
  have h_expand : latticeTestField eval f =
      ∑ x : Fin n, (latticeTestField eval f x) •
        (Pi.single x (1 : ℝ) : FiniteLatticeField n) := by
    funext y
    simp [latticeTestField, Pi.single_apply]
  rw [h_expand, map_sum]
  simp only [map_smul, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp [latticeTestField, mul_comm]

/-- Concrete finite-lattice consumer: a source L² bound for the weighted
coordinate sum transfers through the explicit finite-sum lift.  This theorem
is a finite-lattice interface only; it asserts no continuum convergence. -/
theorem latticeEmbedLift_pushforward_eval_L2_norm_le
    {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (μ : Measure Ω) (embed : Ω → FiniteLatticeConfiguration n)
    (eval : Fin n → E →L[ℝ] ℝ) (f : E) (g : Ω → ℝ) (C : ℝ)
    (h_embed : Measurable embed)
    (h_eval : ∀ᵐ ω ∂μ,
      (∑ x : Fin n, (embed ω) (Pi.single x (1 : ℝ)) * eval x f) = g ω)
    (h_source : (eLpNorm g (2 : ENNReal) μ).toReal ≤ C) :
    (eLpNorm (fun η : WeakDual ℝ E => η f) (2 : ENNReal)
      (Measure.map (latticeEmbedLift eval ∘ embed) μ)).toReal ≤ C := by
  exact pushforward_eval_L2_norm_le μ (latticeEmbedLift eval ∘ embed)
    (latticeEmbedLift_measurable eval |>.comp h_embed) f g
    (by filter_upwards [h_eval] with ω hω; simpa [latticeEmbedLift_eval] using hω)
    C h_source

/-- Uniform finite-lattice form of the concrete consumer. -/
theorem latticeEmbedLift_uniform_pushforward_eval_L2_norm_le
    {ι : Type*} {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (μ : ι → Measure Ω) (embed : ι → Ω → FiniteLatticeConfiguration n)
    (eval : Fin n → E →L[ℝ] ℝ) (f : E) (g : ι → Ω → ℝ) (C : ℝ)
    (h_embed : ∀ i, Measurable (embed i))
    (h_eval : ∀ i, ∀ᵐ ω ∂μ i,
      (∑ x : Fin n, (embed i ω) (Pi.single x (1 : ℝ)) * eval x f) = g i ω)
    (h_source : ∀ i, (eLpNorm (g i) (2 : ENNReal) (μ i)).toReal ≤ C) :
    ∀ i, (eLpNorm (fun η : WeakDual ℝ E => η f) (2 : ENNReal)
      (Measure.map (latticeEmbedLift eval ∘ embed i) (μ i))).toReal ≤ C := by
  intro i
  exact latticeEmbedLift_pushforward_eval_L2_norm_le (μ i) (embed i) eval f
    (g i) C (h_embed i) (h_eval i) (h_source i)

/-- A clean GJ-shaped covariance certificate: the covariance CLM and the
summable Gaussian series coefficients are explicit inputs.  The CLM is not
claimed to be the upstream spectral `latticeCovarianceGJ`; that spectral
construction remains outside this clean project. -/
structure LatticeCovarianceGJData
    {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] where
  latticeCovarianceGJ : FiniteLatticeField n →L[ℝ] H
  coefficients : ℕ → H
  coefficients_summable : Summable (fun k => ‖coefficients k‖)

/-- The exact GJ lattice-spacing rescaling, separated from the upstream
spectral construction of the bare covariance. -/
structure LatticeCovarianceGJRescalingData
    {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] where
  latticeSpacing : ℝ
  latticeDimension : ℕ
  latticeSpacing_pos : 0 < latticeSpacing
  bareCovariance : FiniteLatticeField n →L[ℝ] H
  coefficients : ℕ → H
  coefficients_summable : Summable (fun k => ‖coefficients k‖)

/-- GJ's normalization `(a^d)^(-1/2) • T`, with `T` kept as an explicit
input because the upstream spectral `T = Q^(-1/2)` is not present here. -/
def LatticeCovarianceGJRescalingData.latticeCovarianceGJ
    {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (D : LatticeCovarianceGJRescalingData (n := n) (H := H)) :
    FiniteLatticeField n →L[ℝ] H :=
  (Real.sqrt (D.latticeSpacing ^ D.latticeDimension))⁻¹ • D.bareCovariance

/-- The GJ normalization scales the covariance bilinear form by
`(a^d)⁻¹`, independently of how the bare covariance was constructed. -/
theorem LatticeCovarianceGJRescalingData.covariance_eq_inv_smul_bare
    {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (D : LatticeCovarianceGJRescalingData (n := n) (H := H))
    (f g : FiniteLatticeField n) :
    @inner ℝ H _ (D.latticeCovarianceGJ f) (D.latticeCovarianceGJ g) =
      (D.latticeSpacing ^ D.latticeDimension : ℝ)⁻¹ *
        @inner ℝ H _ (D.bareCovariance f) (D.bareCovariance g) := by
  unfold LatticeCovarianceGJRescalingData.latticeCovarianceGJ
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
  have hp : (0 : ℝ) < D.latticeSpacing ^ D.latticeDimension :=
    pow_pos D.latticeSpacing_pos _
  have hs : Real.sqrt (D.latticeSpacing ^ D.latticeDimension) *
      Real.sqrt (D.latticeSpacing ^ D.latticeDimension) =
      D.latticeSpacing ^ D.latticeDimension :=
    Real.mul_self_sqrt (le_of_lt hp)
  simp
  rw [show (Real.sqrt (D.latticeSpacing ^ D.latticeDimension))⁻¹ *
      ((Real.sqrt (D.latticeSpacing ^ D.latticeDimension))⁻¹ *
        @inner ℝ H _ (D.bareCovariance f) (D.bareCovariance g)) =
      ((Real.sqrt (D.latticeSpacing ^ D.latticeDimension))⁻¹ *
        (Real.sqrt (D.latticeSpacing ^ D.latticeDimension))⁻¹) *
        @inner ℝ H _ (D.bareCovariance f) (D.bareCovariance g) by ring]
  congr 1
  rw [show (Real.sqrt (D.latticeSpacing ^ D.latticeDimension))⁻¹ *
      (Real.sqrt (D.latticeSpacing ^ D.latticeDimension))⁻¹ =
      (Real.sqrt (D.latticeSpacing ^ D.latticeDimension) *
        Real.sqrt (D.latticeSpacing ^ D.latticeDimension))⁻¹ by rw [mul_inv]]
  rw [hs]

/-- The rescaled covariance is positive semidefinite on the diagonal. -/
theorem LatticeCovarianceGJRescalingData.covariance_self_nonneg
    {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (D : LatticeCovarianceGJRescalingData (n := n) (H := H))
    (f : FiniteLatticeField n) :
    0 ≤ @inner ℝ H _ (D.latticeCovarianceGJ f) (D.latticeCovarianceGJ f) := by
  rw [D.covariance_eq_inv_smul_bare]
  have hp0 : 0 ≤ (D.latticeSpacing ^ D.latticeDimension : ℝ) :=
    le_of_lt (pow_pos D.latticeSpacing_pos _)
  have hp : 0 ≤ (D.latticeSpacing ^ D.latticeDimension : ℝ)⁻¹ :=
    inv_nonneg.mpr hp0
  exact mul_nonneg hp real_inner_self_nonneg

def LatticeCovarianceGJRescalingData.gaussianMeasure
    {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (D : LatticeCovarianceGJRescalingData (n := n) (H := H)) :
    Measure (WeakDual ℝ (FiniteLatticeField n)) :=
  gaussianWeakDualMeasure D.latticeCovarianceGJ D.coefficients

@[simp] theorem LatticeCovarianceGJRescalingData.gaussianMeasure_isProbability
    {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (D : LatticeCovarianceGJRescalingData (n := n) (H := H)) :
    IsProbabilityMeasure D.gaussianMeasure := by
  unfold LatticeCovarianceGJRescalingData.gaussianMeasure
  infer_instance

/-- Concrete Gaussian continuum second-moment consumer for the clean
GJ-shaped certificate. -/
theorem latticeCovarianceGJData_gaussian_pushforward_eval_L2_norm_le
    {n : ℕ} {E H : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (D : LatticeCovarianceGJData (n := n) (H := H))
    (eval : Fin n → E →L[ℝ] ℝ) (f : E) :
    (eLpNorm (fun η : WeakDual ℝ E => η f) (2 : ENNReal)
      (Measure.map (latticeEmbedLift eval)
        (gaussianWeakDualMeasure D.latticeCovarianceGJ D.coefficients))).toReal ≤
      (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
        (‖D.latticeCovarianceGJ (latticeTestField eval f)‖ *
          ∑' k, ‖D.coefficients k‖) := by
  exact latticeEmbedLift_pushforward_eval_L2_norm_le
    (gaussianWeakDualMeasure D.latticeCovarianceGJ D.coefficients)
    (fun ω => ω) eval f
    (fun ω => ω (latticeTestField eval f))
    ((eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
      (‖D.latticeCovarianceGJ (latticeTestField eval f)‖ *
        ∑' k, ‖D.coefficients k‖))
    measurable_id
    (by
      filter_upwards [] with ω
      calc
        (∑ x : Fin n, ω (Pi.single x (1 : ℝ)) * eval x f) =
            latticeEmbedLift eval ω f := (latticeEmbedLift_eval eval ω f).symm
        _ = ω (latticeTestField eval f) := latticeEmbedLift_eval_eq eval ω f)
    (gaussianWeakDualMeasure_eval_L2_norm_bound
      D.latticeCovarianceGJ D.coefficients D.coefficients_summable
      (latticeTestField eval f))

/-- The rescaling certificate feeds the same concrete Gaussian consumer. -/
theorem latticeCovarianceGJRescalingData_gaussian_pushforward_eval_L2_norm_le
    {n : ℕ} {E H : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (D : LatticeCovarianceGJRescalingData (n := n) (H := H))
    (eval : Fin n → E →L[ℝ] ℝ) (f : E) :
    (eLpNorm (fun η : WeakDual ℝ E => η f) (2 : ENNReal)
      (Measure.map (latticeEmbedLift eval) D.gaussianMeasure)).toReal ≤
      (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
        (‖D.latticeCovarianceGJ (latticeTestField eval f)‖ *
          ∑' k, ‖D.coefficients k‖) := by
  exact latticeCovarianceGJData_gaussian_pushforward_eval_L2_norm_le
    { latticeCovarianceGJ := D.latticeCovarianceGJ
      coefficients := D.coefficients
      coefficients_summable := D.coefficients_summable } eval f

/-- Uniform family version of the rescaling certificate.  The hypothesis is
exactly the remaining source-side uniform estimate; no lattice-to-continuum
limit is inferred from it. -/
theorem latticeCovarianceGJRescalingData_uniform_gaussian_pushforward_eval_L2_norm_le
    {ι : Type*} {n : ℕ} {E H : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (D : ι → LatticeCovarianceGJRescalingData (n := n) (H := H))
    (eval : Fin n → E →L[ℝ] ℝ) (f : E) (C : ℝ)
    (h_source : ∀ i,
      (eLpNorm id (2 : ENNReal) (gaussianReal (0 : ℝ) 1)).toReal *
        (‖(D i).latticeCovarianceGJ (latticeTestField eval f)‖ *
          ∑' k, ‖(D i).coefficients k‖) ≤ C) :
    ∀ i, (eLpNorm (fun η : WeakDual ℝ E => η f) (2 : ENNReal)
      (Measure.map (latticeEmbedLift eval) (D i).gaussianMeasure)).toReal ≤ C := by
  intro i
  exact (latticeCovarianceGJRescalingData_gaussian_pushforward_eval_L2_norm_le
    (D i) eval f).trans (h_source i)

/-- GJ-facing name for the pushforward estimate.  A concrete
`latticeCovarianceGJ` instance supplies `g`, `h_eval`, and `hC`; the theorem
then transfers its source L² estimate through `latticeEmbedLift`. -/
theorem latticeCovarianceGJ_pushforward_eval_L2_norm_le
    {Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (latticeGaussianMeasure : Measure Ω)
    (latticeEmbedLift : Ω → WeakDual ℝ E)
    (h_embed_measurable : Measurable latticeEmbedLift)
    (f : E) (lattice_eval : Ω → ℝ)
    (h_latticeEmbedLift_eval : ∀ᵐ ω ∂latticeGaussianMeasure,
      latticeEmbedLift ω f = lattice_eval ω)
    (C : ℝ)
    (h_lattice_second_moment :
      (eLpNorm lattice_eval (2 : ENNReal) latticeGaussianMeasure).toReal ≤ C) :
    (eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal)
      (Measure.map latticeEmbedLift latticeGaussianMeasure)).toReal ≤ C :=
  pushforward_eval_L2_norm_le latticeGaussianMeasure latticeEmbedLift
    h_embed_measurable f lattice_eval h_latticeEmbedLift_eval C
    h_lattice_second_moment

/-- The bundled uniform certificate produces the pushed-forward estimate
without re-exposing its bookkeeping fields. -/
theorem latticeCovarianceGJ_uniform_data_eval_L2_norm_le
    {ι Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (D : LatticeGaussianUniformData (ι := ι) (Ω := Ω) (E := E)) (f : E) :
    ∀ i, (eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal)
      (Measure.map (D.latticeEmbedLift i) (D.latticeGaussianMeasure i))).toReal ≤ D.bound := by
  intro i
  exact latticeCovarianceGJ_pushforward_eval_L2_norm_le
    (D.latticeGaussianMeasure i) (D.latticeEmbedLift i) (D.embed_measurable i)
    f (D.lattice_eval i f) (D.embed_eval_ae i f) D.bound
    (D.source_L2_bound i f)

/-- Uniform version for a family of lattice approximations.  It is the direct
consumer shape for a uniform `latticeCovarianceGJ` covariance estimate. -/
theorem latticeCovarianceGJ_uniform_pushforward_eval_L2_norm_le
    {ι Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (latticeGaussianMeasure : ι → Measure Ω)
    (latticeEmbedLift : ι → Ω → WeakDual ℝ E)
    (h_embed_measurable : ∀ i, Measurable (latticeEmbedLift i))
    (f : E) (lattice_eval : ι → Ω → ℝ) (C : ℝ)
    (h_eval : ∀ i, ∀ᵐ ω ∂latticeGaussianMeasure i,
      latticeEmbedLift i ω f = lattice_eval i ω)
    (h_lattice_second_moment : ∀ i,
      (eLpNorm (lattice_eval i) (2 : ENNReal)
        (latticeGaussianMeasure i)).toReal ≤ C) :
    ∀ i, (eLpNorm (fun ω : WeakDual ℝ E => ω f) (2 : ENNReal)
      (Measure.map (latticeEmbedLift i) (latticeGaussianMeasure i))).toReal ≤ C := by
  intro i
  exact latticeCovarianceGJ_pushforward_eval_L2_norm_le
    (latticeGaussianMeasure i) (latticeEmbedLift i) (h_embed_measurable i)
    f (lattice_eval i) (h_eval i) C (h_lattice_second_moment i)

end Pphi2Clean.Continuum
