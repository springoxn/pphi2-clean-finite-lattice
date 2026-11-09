import AImathPPhi2Clean.PeriodicHMinusThreeWeakLimitMarginal
import AImathPPhi2Clean.PeriodicFS4DProbeMoment

#check @Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders
#print axioms Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders
#check @Pphi2Clean.Continuum.fs4PeriodicFixedVolume_weak_tendsto_free
#print axioms Pphi2Clean.Continuum.fs4PeriodicFixedVolume_weak_tendsto_free

example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ μfree : MeasureTheory.ProbabilityMeasure
      Pphi2Clean.Continuum.PeriodicHMinusThreeCompletion,
      Pphi2Clean.Continuum.periodicHMinusThreeFixedVolumeFreeFieldWeakLimit
        L mass hL hmass μfree := by
  obtain ⟨μ, hμ, _⟩ :=
    Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders
      L mass hL hmass
  exact ⟨μ, hμ⟩

example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Filter.Tendsto
      (Pphi2Clean.Continuum.fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass)
      Filter.atTop
      (nhds (Pphi2Clean.Continuum.fs4GaussianCarrierProbabilityMeasure L mass)) :=
  Pphi2Clean.Continuum.fs4PeriodicFixedVolume_weak_tendsto_free L mass hL hmass
