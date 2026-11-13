import AImathPPhi2Clean.Periodic3DCanonicalCovariance

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology Pphi2Clean.UpstreamLattice

theorem periodic3DCanonicalProjection_eq_resolventTarget
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (hjs : Function.Injective js)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0)) :
    (periodic3DGaussianTargetMeasure L mass).map
      (periodic3DCanonicalCoordinateProjection js) =
      periodicResolventTargetMeasure 3 m L mass hmass
        (fun i => periodic3DPhysicalCoordinateTest L hL (js i)) := by
  apply periodic3DCanonicalProjection_eq_resolventTarget_of_covariance
    L mass hL hmass js hjs hsupport
  intro i j
  rw [periodic3DPhysicalCoordinateTest_resolventCovarianceMatrix m L mass hL hmass js hjs hsupport]
  congr 1
  rw [inv_pow, Real.sq_sqrt hL.le]
  ring

def periodic3DCoordinateMode (j : FS4GaussianRealCoordinateIndex) : Periodic3DIndex :=
  j.elim (fun _ => 0) (fun q => periodic3DRestrictIndex q.1.1)

def periodic3DCoordinateUseSine (j : FS4GaussianRealCoordinateIndex) : Bool :=
  j.elim (fun _ => false) (fun q => q.2)

theorem periodic3DPhysicalCoordinateTest_eq_fourierFamily
    {m : ℕ} (L : ℝ) (hL : 0 < L) (js : Fin m → FS4GaussianRealCoordinateIndex) :
    (fun i => periodic3DPhysicalCoordinateTest L hL (js i)) =
      periodic3DFourierTestFamily L hL
        (fun i => periodic3DCoordinateMode (js i))
        (fun i => periodic3DCoordinateUseSine (js i)) := by
  funext i
  simp only [periodic3DFourierTestFamily, periodicFourierTestFamily]
  rcases hj : js i with u | ⟨k, b⟩
  · rfl
  · cases b <;> rfl

theorem periodic3DCanonicalProjection_eq_fourierFamily
    {m : ℕ} (L : ℝ) (hL : 0 < L) (js : Fin m → FS4GaussianRealCoordinateIndex) :
    periodic3DCanonicalCoordinateProjection js = periodic3DFourierFamilyProjection L hL
      (fun i => periodic3DCoordinateMode (js i))
      (fun i => periodic3DCoordinateUseSine (js i)) := by
  funext x
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).injective
  funext i
  simp only [PiLp.continuousLinearEquiv_apply, periodic3DCanonicalCoordinateProjection,
    periodic3DFourierFamilyProjection, WithLp.ofLp_toLp]
  rcases hj : js i with u | ⟨k, b⟩
  · have he : periodic3DExtend (0 : Periodic3DIndex) = (0 : FS4Index) := by
      funext j
      fin_cases j <;> simp [periodic3DExtend]
    have hw : periodic3DHminusFourWeight (0 : Periodic3DIndex) = 1 := by
      change fs4SobolevWeight 4 (periodic3DExtend 0) = 1
      rw [he, fs4SobolevWeight_zero]
    simp [periodic3DCoordinateMode, periodic3DCoordinateUseSine, hw]
  · cases b <;> rfl

def periodic3DGaussianTargetProbabilityMeasure (L mass : ℝ) :
    ProbabilityMeasure Periodic3DCompletion := ⟨periodic3DGaussianTargetMeasure L mass, inferInstance⟩

theorem periodic3DFixedVolume_canonicalMarginal_tendsto
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (hjs : Function.Injective js)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun q => q.1.1 3 = 0)) :
    Tendsto (fun n => (periodic3DFixedVolumeProbabilityMeasure L mass hL hmass n).map
      (periodic3DCanonicalCoordinateProjection js)) atTop
      (𝓝 ((periodic3DGaussianTargetProbabilityMeasure L mass).map
        (periodic3DCanonicalCoordinateProjection js))) := by
  have heq : (periodic3DGaussianTargetProbabilityMeasure L mass).map
      (periodic3DCanonicalCoordinateProjection js) =
      periodicResolventTargetProbabilityMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL (fun i => periodic3DCoordinateMode (js i))
          (fun i => periodic3DCoordinateUseSine (js i))) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    change (periodic3DGaussianTargetMeasure L mass).map
      (periodic3DCanonicalCoordinateProjection js) =
      periodicResolventTargetMeasure 3 m L mass hmass _
    rw [← periodic3DPhysicalCoordinateTest_eq_fourierFamily L hL js]
    exact periodic3DCanonicalProjection_eq_resolventTarget L mass hL hmass js hjs hsupport
  rw [heq, periodic3DCanonicalProjection_eq_fourierFamily L hL js]
  exact periodic3DFixedVolume_fourierFamily_marginal_tendsto m L mass hL hmass _ _

end Pphi2Clean.Continuum
