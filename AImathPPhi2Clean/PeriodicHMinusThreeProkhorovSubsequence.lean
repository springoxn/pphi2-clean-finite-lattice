import AImathPPhi2Clean.PeriodicHMinusThreeFixedVolumeTightness
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology ProbabilityTheory Filter

/-- The concrete probability-measure set associated with a sequence on the
completed periodic H^-3 carrier. -/
def periodicHMinusThreeProbabilityMeasureSet
    (μ : ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion) :
    Set (ProbabilityMeasure PeriodicHMinusThreeCompletion) :=
  Set.range μ

/-- Tightness of the concrete fixed-volume lattice laws, viewed as a set of
probability measures rather than as an informal family of finite marginals. -/
theorem periodicHMinusThree_fixedVolume_probabilityMeasureSet_tight
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    IsTightMeasureSet
      {ρ : Measure PeriodicHMinusThreeCompletion |
        ∃ n, ρ =
          (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
            L mass hL hmass n : Measure PeriodicHMinusThreeCompletion)} := by
  refine (isTightMeasureSet_iff_exists_isCompact_measure_compl_le).2 ?_
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ρ hρ
    simp [htop]
  · have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    obtain ⟨K, hK, hbound⟩ :=
      periodicHMinusThree_fixedVolume_freeField_tight L mass hL hmass
        ε.toReal hεreal
    refine ⟨K, hK, ?_⟩
    intro ρ hρ
    rcases hρ with ⟨n, rfl⟩
    rw [← ENNReal.ofReal_toReal htop]
    exact hbound n

/-- Prokhorov subsequence extraction on the actual Borel probability-measure
space. Every subsequence of the fixed-volume lattice laws has a further
subsequence converging to a `ProbabilityMeasure PeriodicHMinusThreeCompletion`.
The limit is not replaced by a finite-dimensional marginal family. -/
theorem periodicHMinusThree_fixedVolume_prokhorov_subsequence
    (hsep : TopologicalSpace.SeparableSpace PeriodicHMinusThreeCompletion)
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop) :
    ∃ (ms : ℕ → ℕ) (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion),
      StrictMono ms ∧
      Tendsto
        (fun k =>
          (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
            L mass hL hmass (ns (ms k))))
        atTop (𝓝 ν) := by
  letI : TopologicalSpace.SeparableSpace PeriodicHMinusThreeCompletion := hsep
  let μ : ℕ → ProbabilityMeasure PeriodicHMinusThreeCompletion :=
    periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure L mass hL hmass
  let S : Set (ProbabilityMeasure PeriodicHMinusThreeCompletion) := Set.range μ
  have htight : IsTightMeasureSet
      {ρ : Measure PeriodicHMinusThreeCompletion | ∃ n, ρ = (μ n : Measure _)} := by
    simpa [μ] using periodicHMinusThree_fixedVolume_probabilityMeasureSet_tight
      L mass hL hmass
  have hcompact : IsCompact (closure S) := by
    apply isCompact_closure_of_isTightMeasureSet
    simpa [S, Set.ext_iff, eq_comm] using htight
  have hseq : ∀ n, μ (ns n) ∈ closure S := by
    intro n
    exact subset_closure ⟨ns n, rfl⟩
  obtain ⟨ν, _hνS, ms, hms, hlim⟩ := hcompact.tendsto_subseq hseq
  refine ⟨ms, ν, hms, ?_⟩
  simpa [Function.comp_def, μ] using hlim

end Pphi2Clean.Continuum
