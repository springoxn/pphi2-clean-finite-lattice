import AImathPPhi2Clean.Periodic3DGaussianWeakLimit

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology

/-- Every finite Fourier family, including repeats and degenerate zero-sine
coordinates, has the actual dimension-three resolvent Gaussian law. -/
theorem periodic3DGaussianTarget_fourierFamily_marginal
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    (periodic3DGaussianTargetProbabilityMeasure L mass).map
      (periodic3DFourierFamilyProjection L hL modes useSine) =
      periodicResolventTargetProbabilityMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine) :=
  periodic3DFixedVolume_weak_limit_fourierFamily m L mass hL hmass modes useSine
    (periodic3DGaussianTargetProbabilityMeasure L mass)
    (periodic3DFixedVolume_weak_tendsto_gaussianTarget L mass hL hmass)

theorem periodic3DGaussianTarget_fourierFamily_measure
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    (periodic3DGaussianTargetMeasure L mass).map
      (periodic3DFourierFamilyProjection L hL modes useSine) =
      periodicResolventTargetMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine) := by
  exact congrArg (fun ρ : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) =>
    (ρ : Measure (EuclideanSpace ℝ (Fin m))))
    (periodic3DGaussianTarget_fourierFamily_marginal m L mass hL hmass modes useSine)

theorem periodic3DGaussianTarget_fourierFamily_hasGaussianLaw
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    HasGaussianLaw id ((periodic3DGaussianTargetMeasure L mass).map
      (periodic3DFourierFamilyProjection L hL modes useSine)) := by
  rw [periodic3DGaussianTarget_fourierFamily_measure m L mass hL hmass modes useSine]
  exact periodicResolventTargetMeasure_hasGaussianLaw 3 m L mass hmass _

theorem periodic3DGaussianTarget_fourierFamily_mean
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool)
    (t : EuclideanSpace ℝ (Fin m)) :
    ∫ z, inner ℝ t z ∂((periodic3DGaussianTargetMeasure L mass).map
      (periodic3DFourierFamilyProjection L hL modes useSine)) = 0 := by
  rw [periodic3DGaussianTarget_fourierFamily_measure m L mass hL hmass modes useSine]
  exact periodicResolventTargetMeasure_mean_zero 3 m L mass hmass _ t

#print axioms periodic3DGaussianTarget_fourierFamily_hasGaussianLaw
#print axioms periodic3DGaussianTarget_fourierFamily_mean

#print axioms periodic3DGaussianTarget_fourierFamily_marginal
#print axioms periodic3DGaussianTarget_fourierFamily_measure
end Pphi2Clean.Continuum
