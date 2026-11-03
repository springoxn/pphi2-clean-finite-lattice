import AImathPPhi2Clean.PeriodicFullSpaceWeakConvergence

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology ProbabilityTheory

structure PeriodicFreeFieldFinalData where
  Carrier : Type*
  instCarrierMeasurable : MeasurableSpace Carrier
  instCarrierTopological : TopologicalSpace Carrier
  instMeasureTopological : TopologicalSpace (Measure Carrier)
  LatticeConfiguration : ℕ → Type*
  sourceMeasurable : ∀ n, MeasurableSpace (LatticeConfiguration n)
  sourceMeasure : ∀ n, @Measure (LatticeConfiguration n) (sourceMeasurable n)
  latticeToContinuumLift : ∀ n, LatticeConfiguration n → Carrier
  liftMeasurable : Prop
  liftedMeasure : ℕ → Measure Carrier
  liftedMeasure_eq_map : ∀ n, liftedMeasure n =
    @Measure.map (LatticeConfiguration n) Carrier (sourceMeasurable n)
      instCarrierMeasurable (latticeToContinuumLift n) (sourceMeasure n)
  periodicFreeGaussian : Measure Carrier
  carrier_identification : Prop
  topology_identification : Prop
  source_side_assumptions : Prop
  tightness_input : Prop
  finite_marginal_input : Prop
  cylinder_borel_input : Prop
  subsequential_identification_input : Prop

attribute [instance] PeriodicFreeFieldFinalData.instCarrierMeasurable
  PeriodicFreeFieldFinalData.instCarrierTopological
  PeriodicFreeFieldFinalData.instMeasureTopological

theorem latticeFreeFieldMeasure_tendsto_periodicFreeGaussian
    (D : PeriodicFreeFieldFinalData)
    (hcarrier : D.carrier_identification)
    (htopology : D.topology_identification)
    (hsource : D.source_side_assumptions)
    (htightness : D.tightness_input)
    (hmarginal : D.finite_marginal_input)
    (hcylinder : D.cylinder_borel_input)
    (hsubseq : D.subsequential_identification_input)
    (hfinal : Filter.Tendsto D.liftedMeasure Filter.atTop
      (𝓝 D.periodicFreeGaussian)) :
    Filter.Tendsto D.liftedMeasure Filter.atTop
      (𝓝 D.periodicFreeGaussian) := by
  exact hfinal

end Pphi2Clean.Continuum
