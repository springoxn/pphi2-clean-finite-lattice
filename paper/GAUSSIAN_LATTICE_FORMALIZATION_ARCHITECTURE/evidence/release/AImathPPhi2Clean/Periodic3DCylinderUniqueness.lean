import AImathPPhi2Clean.Periodic3DTightness

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Pphi2Clean.UpstreamLattice

theorem periodic3DHminusFour_coordinate_continuous (k : Periodic3DIndex) :
    Continuous (fun x : Periodic3DCompletion => x k) :=
  (lp.evalCLM ℝ (fun _ : Periodic3DIndex => ℂ) 2 k).continuous

def periodic3DHminusFourCoordinateCylinder
    (s : Finset Periodic3DIndex) (S : Set (∀ i : s, ℂ)) : Set Periodic3DCompletion :=
  (fun x : Periodic3DCompletion => s.restrict (x : Periodic3DIndex → ℂ)) ⁻¹' S
def periodic3DHminusFourMeasurableCylinders : Set (Set Periodic3DCompletion) :=
  {A | ∃ t ∈ measurableCylinders (fun _ : Periodic3DIndex => ℂ),
    (fun x : Periodic3DCompletion => (x : Periodic3DIndex → ℂ)) ⁻¹' t = A}
theorem measurable_periodic3DHminusFour_coordinate_inclusion :
    Measurable (fun x : Periodic3DCompletion =>
      (x : Periodic3DIndex → ℂ)) := by
  rw [measurable_pi_iff]
  intro k
  exact (periodic3DHminusFour_coordinate_continuous k).measurable
theorem periodic3DHminusFour_cylinder_mem
    (s : Finset Periodic3DIndex) {S : Set (∀ i : s, ℂ)} (hS : MeasurableSet S) :
    periodic3DHminusFourCoordinateCylinder s S ∈ periodic3DHminusFourMeasurableCylinders := by
  refine ⟨cylinder s S, ?_, ?_⟩
  · rw [mem_measurableCylinders]
    exact ⟨s, S, hS, rfl⟩
  · rfl
theorem periodic3DHminusFour_norm_sq_sublevel_measurable_of_generated_cylinders
    (y : Periodic3DCompletion) (r : ℝ) :
    @MeasurableSet Periodic3DCompletion
      (MeasurableSpace.generateFrom periodic3DHminusFourMeasurableCylinders)
      {x | ‖x - y‖ ^ 2 < r} := by
  letI : MeasurableSpace Periodic3DCompletion :=
    MeasurableSpace.generateFrom periodic3DHminusFourMeasurableCylinders
  have hcoord : ∀ i : Periodic3DIndex, Measurable (fun x : Periodic3DCompletion => x i) := by
    intro i A hA
    let j : {k // k ∈ ({i} : Finset Periodic3DIndex)} := ⟨i, by simp⟩
    have hS : MeasurableSet {z : ∀ k : ({i} : Finset Periodic3DIndex), ℂ | z j ∈ A} :=
      hA.preimage (measurable_pi_apply j)
    have hcyl := periodic3DHminusFour_cylinder_mem ({i} : Finset Periodic3DIndex) hS
    have heq : Set.preimage (fun x : Periodic3DCompletion => x i) A =
        periodic3DHminusFourCoordinateCylinder {i} {z | z j ∈ A} := by
      ext x
      rfl
    rw [heq]
    exact MeasurableSpace.measurableSet_generateFrom hcyl
  have hsum : Measurable (fun x : Periodic3DCompletion =>
      ∑' i : Periodic3DIndex, ‖x i - y i‖ ^ 2) :=
    Measurable.tsum (fun i => ((hcoord i).sub measurable_const).norm.pow_const 2)
  have hnorm : Measurable (fun x : Periodic3DCompletion => ‖x - y‖ ^ 2) := by
    convert hsum using 1
    funext x
    simpa using (lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ENNReal).toReal) (x - y))
  exact measurableSet_Iio.preimage hnorm
def Periodic3DCylinderBorelGenerationInput : Prop :=
  MeasurableSpace.generateFrom periodic3DHminusFourMeasurableCylinders =
    borel Periodic3DCompletion
open TopologicalSpace in
theorem periodic3DHminusFour_cylinder_borel_generation : Periodic3DCylinderBorelGenerationInput := by
  letI : TopologicalSpace.SeparableSpace Periodic3DCompletion :=
    periodic3DHminusFourCompletion_separable
  haveI : SecondCountableTopology Periodic3DCompletion := inferInstance
  change MeasurableSpace.generateFrom periodic3DHminusFourMeasurableCylinders =
    borel Periodic3DCompletion
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨t, ht, rfl⟩
    rw [mem_measurableCylinders] at ht
    rcases ht with ⟨s, S, hS, rfl⟩
    exact hS.preimage ((Finset.measurable_restrict s).comp
      measurable_periodic3DHminusFour_coordinate_inclusion)
  · letI : MeasurableSpace Periodic3DCompletion :=
      MeasurableSpace.generateFrom periodic3DHminusFourMeasurableCylinders
    have hball (y : Periodic3DCompletion) (r : ℝ) (hr : 0 < r) :
        MeasurableSet (Metric.ball y r) := by
      have heq : Metric.ball y r = {x | ‖x - y‖ ^ 2 < r ^ 2} := by
        ext x
        simp only [Metric.mem_ball, dist_eq_norm, Set.mem_setOf_eq]
        constructor <;> intro h <;> nlinarith [norm_nonneg (x - y)]
      rw [heq]
      exact periodic3DHminusFour_norm_sq_sublevel_measurable_of_generated_cylinders y (r ^ 2)
    apply MeasurableSpace.generateFrom_le
    intro U hU
    change IsOpen U at hU
    let F : Set (Set Periodic3DCompletion) :=
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
          (Metric.isOpen_iff (α := Periodic3DCompletion)).mp hU x hx
        exact Set.mem_sUnion.mpr
          ⟨Metric.ball x r, ⟨x, r, hr, rfl, hsub⟩, Metric.mem_ball_self hr⟩
    obtain ⟨v, hv, hvF, hvcover⟩ := isOpen_sUnion_countable F hFopen
    rw [← hFcover, ← hvcover]
    apply MeasurableSet.sUnion hv
    intro V hV
    rcases hvF hV with ⟨y, r, hr, rfl, hsub⟩
    exact hball y r hr
theorem periodic3DHminusFour_measure_ext_of_cylinder
    (μ ν : Measure Periodic3DCompletion)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : ∀ (s : Finset Periodic3DIndex) (S : Set (∀ i : s, ℂ)),
      MeasurableSet S →
        μ (periodic3DHminusFourCoordinateCylinder s S) =
          ν (periodic3DHminusFourCoordinateCylinder s S))
    (huniv : μ (Set.univ) = ν (Set.univ)) : μ = ν := by
  apply ext_of_generate_finite periodic3DHminusFourMeasurableCylinders
    periodic3DHminusFour_cylinder_borel_generation.symm
    (isPiSystem_measurableCylinders.comap
      (fun x : Periodic3DCompletion => (x : Periodic3DIndex → ℂ)))
  · intro A hA
    rcases hA with ⟨t, ht, rfl⟩
    rcases (mem_measurableCylinders t).mp ht with ⟨s, S, hS, rfl⟩
    exact hμν s S hS
  · simpa using huniv

theorem periodic3DHminusFour_probabilityMeasure_ext_of_finite_marginals
    (μ ν : ProbabilityMeasure Periodic3DCompletion)
    (hmarg : ∀ (s : Finset Periodic3DIndex),
      μ.map (fun x : Periodic3DCompletion =>
        s.restrict (x : Periodic3DIndex → ℂ)) =
      ν.map (fun x : Periodic3DCompletion =>
        s.restrict (x : Periodic3DIndex → ℂ))) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply periodic3DHminusFour_measure_ext_of_cylinder (μ := μ) (ν := ν)
  · intro s S hS
    have hmeas : Measurable (fun x : Periodic3DCompletion =>
        s.restrict (x : Periodic3DIndex → ℂ)) :=
      (Finset.measurable_restrict s).comp
        measurable_periodic3DHminusFour_coordinate_inclusion
    change (μ : Measure Periodic3DCompletion)
        (periodic3DHminusFourCoordinateCylinder s S) =
      (ν : Measure Periodic3DCompletion)
        (periodic3DHminusFourCoordinateCylinder s S)
    rw [periodic3DHminusFourCoordinateCylinder]
    rw [← Measure.map_apply hmeas hS, ← Measure.map_apply hmeas hS]
    exact congrArg
      (fun ρ : ProbabilityMeasure (∀ i : s, ℂ) =>
        (ρ : Measure (∀ i : s, ℂ)) S) (hmarg s)
  · simp [ProbabilityMeasure.coeFn_def]
end Pphi2Clean.Continuum
