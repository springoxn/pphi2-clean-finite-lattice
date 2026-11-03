import AImathPPhi2Clean.PeriodicHMinusThreeProkhorovSubsequence
import AImathPPhi2Clean.PeriodicHMinusThreeCylinderConvergence
import AImathPPhi2Clean.PeriodicHMinusThreeTopologyBorel
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology ProbabilityTheory Filter

/-- A weak limit on the completed periodic H^-3 carrier inherits the expected
finite Fourier marginal. The proof uses continuous mapping of probability
measures and uniqueness of limits in the finite-dimensional probability-measure
space; the finite-cylinder convergence is an explicit input from the preceding
step. -/
theorem periodicHMinusThree_weak_limit_has_expected_cylinder_marginal
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → PeriodicFourierIndex)
    (μ : ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (ns ms : ℕ → ℕ)
    (hms : StrictMono ms)
    (hns : Tendsto ns atTop atTop)
    (hlim : Tendsto (fun k => μ (ns (ms k))) atTop (𝓝 ν))
    (hcyl : Tendsto
      (fun n => (μ n).map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      atTop
      (𝓝 ((periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map (f := periodicHMinusThreeComplexifyCylinder m modes)
        ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable)))) :
    ν.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
      (periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map (f := periodicHMinusThreeComplexifyCylinder m modes)
        ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable) := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ hlim (continuous_periodicHMinusThree_cylinderMap m modes)
  have hms_top : Tendsto ms atTop atTop := hms.tendsto_atTop
  have hsub_top : Tendsto (fun k => ns (ms k)) atTop atTop :=
    hns.comp hms_top
  have hcyl_sub := hcyl.comp hsub_top
  have hmap' : Tendsto
      (fun k => (μ (ns (ms k))).map (f := periodicHMinusThreeCylinderMap m modes)
        ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      atTop (𝓝 (ν.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))) := by
    simpa using hmap
  exact tendsto_nhds_unique hmap' hcyl_sub

theorem periodicHMinusThree_fixedVolume_subsequential_limit_has_expected_cylinder
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → PeriodicFourierIndex)
    (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (ns ms : ℕ → ℕ) (hms : StrictMono ms)
    (hns : Tendsto ns atTop atTop)
    (hlim : Tendsto
      (fun k => periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
        L mass hL hmass (ns (ms k))) atTop (𝓝 ν)) :
    ν.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
      (periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map (f := periodicHMinusThreeComplexifyCylinder m modes)
        ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable) := by
  let μ := periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence L mass hL hmass
  have hcyl : Tendsto
      (fun n => (μ n).map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      atTop
      (𝓝 ((periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map (f := periodicHMinusThreeComplexifyCylinder m modes)
        ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable))) := by
    simpa [μ, periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence] using
      periodicHMinusThreeFixedVolumeMeasureSequence_cylinder_tendsto
        m L mass hL hmass modes
  exact periodicHMinusThree_weak_limit_has_expected_cylinder_marginal
    m L mass hL hmass modes μ ν ns ms hms hns hlim hcyl

/-- Equality of all indexed finite-coordinate marginals determines a Borel
probability measure on the concrete carrier. -/
theorem periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals
    (μ ν : ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (hmarg : ∀ (m : ℕ) (modes : Fin m → PeriodicFourierIndex),
      μ.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
        ν.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable)) :
    μ = ν := by
  have hgen : PeriodicHMinusThreeCylinderBorelGenerationInput :=
    periodicHMinusThree_cylinder_sigma_eq_borel_of_polish
      (periodicHMinusThree_polish_of_separable_input
        periodicHMinusThreeCompletion_separable)
  apply periodicHMinusThree_probabilityMeasure_ext_of_finite_marginals hgen μ ν
  intro s
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let modes : Fin (Fintype.card s) → PeriodicFourierIndex := fun i => (e.symm i).1
  let reindex : (Fin (Fintype.card s) → ℂ) → (∀ i : s, ℂ) := fun y i => y (e i)
  have hreindex : Measurable reindex := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (e i)
  have hcyl : Measurable (periodicHMinusThreeCylinderMap (Fintype.card s) modes) :=
    (continuous_periodicHMinusThree_cylinderMap (Fintype.card s) modes).measurable
  have hcoordMap :
      (fun x : PeriodicHMinusThreeCompletion =>
        s.restrict (x : PeriodicFourierIndex → ℂ)) =
      reindex ∘ periodicHMinusThreeCylinderMap (Fintype.card s) modes := by
    funext x i
    simp [reindex, modes, periodicHMinusThreeCylinderMap]
  have hlam : Measurable (fun x : PeriodicHMinusThreeCompletion =>
      s.restrict (x : PeriodicFourierIndex → ℂ)) :=
    (Finset.measurable_restrict s).comp
      measurable_periodicHMinusThree_coordinate_inclusion
  have hμ : μ.map
        (f := (fun x : PeriodicHMinusThreeCompletion =>
          s.restrict (x : PeriodicFourierIndex → ℂ))) hlam.aemeasurable =
      (μ.map (f := periodicHMinusThreeCylinderMap (Fintype.card s) modes)
        hcyl.aemeasurable).map (f := reindex) hreindex.aemeasurable := by
    apply Subtype.ext
    -- The coercion on a `ProbabilityMeasure` is `toMeasure`, and the lemma that
    -- computes `toMeasure` of a `map` is `rfl`, so this goal is already the
    -- `Measure`-level identity: the two maps compose.
    exact ((MeasureTheory.Measure.map_map hreindex hcyl).trans
      (congrArg (fun g => (μ : Measure PeriodicHMinusThreeCompletion).map g)
        hcoordMap.symm)).symm
  have hν : ν.map
        (f := (fun x : PeriodicHMinusThreeCompletion =>
          s.restrict (x : PeriodicFourierIndex → ℂ))) hlam.aemeasurable =
      (ν.map (f := periodicHMinusThreeCylinderMap (Fintype.card s) modes)
        hcyl.aemeasurable).map (f := reindex) hreindex.aemeasurable := by
    apply Subtype.ext
    exact ((MeasureTheory.Measure.map_map hreindex hcyl).trans
      (congrArg (fun g => (ν : Measure PeriodicHMinusThreeCompletion).map g)
        hcoordMap.symm)).symm
  rw [hμ, hν, hmarg (Fintype.card s) modes]

/-- Tightness, concrete separability, finite-cylinder convergence, and Borel
cylinder uniqueness produce a common weak limit for the complete fixed-volume
probability-measure sequence. -/
theorem periodicHMinusThree_fixedVolume_weak_limit_exists
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion,
      periodicHMinusThreeFixedVolumeFreeFieldWeakLimit L mass hL hmass μfree := by
  let μ := periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence L mass hL hmass
  have hid : Tendsto (fun n : ℕ => n) atTop atTop := tendsto_id
  obtain ⟨m0, μfree, hm0, hlim0⟩ :=
    periodicHMinusThree_fixedVolume_prokhorov_subsequence
      periodicHMinusThreeCompletion_separable L mass hL hmass
      (fun n : ℕ => n) hid
  have hwhole : Tendsto μ atTop (𝓝 μfree) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, ν, hms, hlim⟩ :=
      periodicHMinusThree_fixedVolume_prokhorov_subsequence
        periodicHMinusThreeCompletion_separable L mass hL hmass ns hns
    have hνmarg : ∀ (m : ℕ) (modes : Fin m → PeriodicFourierIndex),
        ν.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
          μfree.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) := by
      intro m modes
      rw [periodicHMinusThree_fixedVolume_subsequential_limit_has_expected_cylinder
          m L mass hL hmass modes ν ns ms hms hns hlim,
        periodicHMinusThree_fixedVolume_subsequential_limit_has_expected_cylinder
          m L mass hL hmass modes μfree (fun n : ℕ => n) m0 hm0 hid hlim0]
    have hνeq : ν = μfree :=
      periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals
        ν μfree hνmarg
    refine ⟨ms, ?_⟩
    simpa [μ, periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence, hνeq] using hlim
  refine ⟨μfree, ?_⟩
  simpa [μ, periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence,
    periodicHMinusThreeFixedVolumeFreeFieldWeakLimit] using hwhole

/-- Every weak limit of the complete fixed-volume sequence has the expected
finite Fourier cylinder marginals. This exposes the identification of the
limit measure as a public theorem rather than leaving it inside the existence
proof above. -/
theorem periodicHMinusThree_fixedVolume_weak_limit_has_expected_cylinder
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (hlim : periodicHMinusThreeFixedVolumeFreeFieldWeakLimit
      L mass hL hmass μfree) :
    ∀ (m : ℕ) (modes : Fin m → PeriodicFourierIndex),
      μfree.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
        (periodicResolventTargetProbabilityMeasure 2
          (Fintype.card (Fin m × Bool)) L mass hmass
          (periodicHMinusThreeCylinderTestFamily m L hL modes)).map (f := periodicHMinusThreeComplexifyCylinder m modes)
          ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable) := by
  intro m modes
  let μ := periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence L mass hL hmass
  have hcyl : Tendsto
      (fun n => (μ n).map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable))
      atTop
      (𝓝 ((periodicResolventTargetProbabilityMeasure 2
        (Fintype.card (Fin m × Bool)) L mass hmass
        (periodicHMinusThreeCylinderTestFamily m L hL modes)).map (f := periodicHMinusThreeComplexifyCylinder m modes)
        ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable))) := by
    simpa [μ, periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence] using
      periodicHMinusThreeFixedVolumeMeasureSequence_cylinder_tendsto
        m L mass hL hmass modes
  exact periodicHMinusThree_weak_limit_has_expected_cylinder_marginal
    m L mass hL hmass modes μ μfree (fun n : ℕ => n) (fun n : ℕ => n)
    strictMono_id tendsto_id hlim hcyl

/-- The identified weak limit is unique among Borel probability measures on
 the concrete carrier. -/
theorem periodicHMinusThree_fixedVolume_weak_limit_unique
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (μ ν : ProbabilityMeasure PeriodicHMinusThreeCompletion)
    (hμ : periodicHMinusThreeFixedVolumeFreeFieldWeakLimit
      L mass hL hmass μ)
    (hν : periodicHMinusThreeFixedVolumeFreeFieldWeakLimit
      L mass hL hmass ν) :
    μ = ν := by
  exact tendsto_nhds_unique hμ hν

/-- Full public form: the fixed-volume sequence has a weak limit and that
limit is identified by every finite Fourier cylinder marginal. -/
theorem periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion,
      periodicHMinusThreeFixedVolumeFreeFieldWeakLimit L mass hL hmass μfree ∧
      ∀ (m : ℕ) (modes : Fin m → PeriodicFourierIndex),
        μfree.map (f := periodicHMinusThreeCylinderMap m modes) ((measurable_periodicHMinusThree_cylinderMap m modes).aemeasurable) =
          (periodicResolventTargetProbabilityMeasure 2
            (Fintype.card (Fin m × Bool)) L mass hmass
            (periodicHMinusThreeCylinderTestFamily m L hL modes)).map
            (f := periodicHMinusThreeComplexifyCylinder m modes)
            ((measurable_periodicHMinusThreeComplexifyCylinder m modes).aemeasurable) := by
  obtain ⟨μfree, hlim⟩ :=
    periodicHMinusThree_fixedVolume_weak_limit_exists L mass hL hmass
  refine ⟨μfree, hlim, ?_⟩
  exact periodicHMinusThree_fixedVolume_weak_limit_has_expected_cylinder
    L mass hL hmass μfree hlim

