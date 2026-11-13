import AImathPPhi2Clean.PeriodicFS4DProbeMoment

#check @Pphi2Clean.Continuum.fs4PhysicalFiniteMarginal_eq_resolventTarget
#print axioms Pphi2Clean.Continuum.fs4PhysicalFiniteMarginal_eq_resolventTarget
#check @Pphi2Clean.Continuum.fs4HminusFour_probabilityMeasure_ext_of_real_finite_marginals
#print axioms Pphi2Clean.Continuum.fs4HminusFour_probabilityMeasure_ext_of_real_finite_marginals
#check @Pphi2Clean.Continuum.fs4Periodic_subsequence_limit_eq_free
#print axioms Pphi2Clean.Continuum.fs4Periodic_subsequence_limit_eq_free
#check @Pphi2Clean.Continuum.fs4PeriodicFixedVolume_weak_tendsto_free
#print axioms Pphi2Clean.Continuum.fs4PeriodicFixedVolume_weak_tendsto_free

-- Independent typed contract: no caller-supplied tightness, target law or marginals.
example (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    Filter.Tendsto
      (Pphi2Clean.Continuum.fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass)
      Filter.atTop
      (nhds (Pphi2Clean.Continuum.fs4GaussianCarrierProbabilityMeasure L mass)) :=
  Pphi2Clean.Continuum.fs4PeriodicFixedVolume_weak_tendsto_free L mass hL hmass
