import AImathPPhi2Clean.PeriodicTorusL2
import AImathPPhi2Clean.PeriodicMassiveEnergy
import AImathPPhi2Clean.PeriodicTorusH1

noncomputable section
open scoped InnerProductSpace
open MeasureTheory
namespace Pphi2Clean.Continuum

/-- Physical-volume pairing with the independently constructed weak resolvent.
The underlying periodic L2 space uses probability Haar measure. -/
def physicalTorusResolventPairing (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) : ℂ :=
  (L : ℂ) ^ d * ⟪physicalTorusTestL2 d L f,
    periodicMassiveResolvent d L mass hmass (physicalTorusTestL2 d L g)⟫_ℂ

/-- The value used in the pairing is an actual weak PDE solution on the
completed trigonometric-polynomial H1 graph, for every energy test. -/
theorem physicalTorusTest_resolvent_isWeakSolution
    (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    periodicIsWeakSolution d L mass hmass (physicalTorusTestL2 d L g)
      (periodicMassiveResolvent d L mass hmass (physicalTorusTestL2 d L g)) :=
  periodicMassiveResolvent_isWeakSolution d L mass hmass (physicalTorusTestL2 d L g)

/-- The physical test source has a unique weak value in the completed H1 graph. -/
theorem physicalTorusTest_resolvent_existsUnique_weak
    (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∃! u : PeriodicL2 d, periodicIsWeakSolution d L mass hmass (physicalTorusTestL2 d L g) u :=
  periodicMassiveResolvent_existsUnique_weak d L mass hmass (physicalTorusTestL2 d L g)

/-- Parseval identifies the physical weak-resolvent pairing with the absolutely
convergent Fourier Green series, with the physical-volume normalization. -/
theorem torusFourierGreenPairing_eq_physicalTorusResolventPairing
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    torusFourierGreenPairing d L mass f g =
      physicalTorusResolventPairing d L mass hmass f g := by
  unfold physicalTorusResolventPairing
  change torusFourierGreenPairing d L mass f g = (L : ℂ) ^ d *
    ⟪physicalTorusTestL2 d L f,
      (periodicMassiveEmbedding d L mass hmass).resolventIn (periodicFourierHilbertBasis d)
        (physicalTorusTestL2 d L g)⟫_ℂ
  rw [MassiveEnergyEmbedding.inner_resolventIn]
  rw [← tsum_mul_left]
  unfold torusFourierGreenPairing
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hf := physicalTorusTestL2_repr d L hL f k
  have hg := physicalTorusTestL2_repr d L hL g k
  change (periodicFourierHilbertBasis d).repr (physicalTorusTestL2 d L f) k = _ at hf
  change (periodicFourierHilbertBasis d).repr (physicalTorusTestL2 d L g) k = _ at hg
  rw [hf, hg]
  have hw : ((periodicMassiveEmbedding d L mass hmass).weight k : ℂ) ^ 2 =
      (torusMassSymbol d L mass k : ℂ)⁻¹ := by
    exact_mod_cast periodicMassiveEmbedding_weight_sq d L mass hmass k
  rw [hw]
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hmc : (torusMassSymbol d L mass k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (torusMassSymbol_pos d L mass hmass k).ne'
  simp only [map_mul, map_pow, map_inv₀, Complex.star_def, Complex.conj_ofReal]
  simp only [inv_pow]
  field_simp [hLc, hmc]

/-- The actual lattice covariance converges to the independent periodic weak
resolvent pairing. No Fourier-interface or convergence hypotheses are required. -/
theorem fixedVolumeCovarianceInner_tendsto_periodicMassiveResolvent
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g) :
    Filter.Tendsto (fixedVolumeCovarianceInner d L mass hL hmass f g)
      Filter.atTop (nhds (physicalTorusResolventPairing d L mass hmass f g).re) := by
  rw [← torusFourierGreenPairing_eq_physicalTorusResolventPairing d L mass hL hmass f g]
  exact fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing d L mass hL hmass f g hf hg

/-- Actual physical GJ mixed moments converge to the weak-resolvent pairing. -/
theorem physicalGJMeasure_fixedVolume_mixedMoment_tendsto_periodicMassiveResolvent
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g) :
    Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          ω f * ω g ∂physicalGJMeasure d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass)
      Filter.atTop (nhds (physicalTorusResolventPairing d L mass hmass f g).re) := by
  rw [← torusFourierGreenPairing_eq_physicalTorusResolventPairing d L mass hL hmass f g]
  exact physicalGJMeasure_fixedVolume_mixedMoment_tendsto_torusFourierGreenPairing
    d L mass hL hmass f g hf hg

/-- The centered covariance of actual physical GJ measures converges to the
periodic weak-resolvent pairing. Both means vanish exactly at every mesh. -/
theorem physicalGJMeasure_fixedVolume_covariance_tendsto_periodicMassiveResolvent
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g) :
    Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        let μ := physicalGJMeasure d N (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
        ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          (ω f - ∫ η, η f ∂μ) * (ω g - ∫ η, η g ∂μ) ∂μ)
      Filter.atTop (nhds (physicalTorusResolventPairing d L mass hmass f g).re) := by
  rw [← torusFourierGreenPairing_eq_physicalTorusResolventPairing d L mass hL hmass f g]
  exact physicalGJMeasure_fixedVolume_covariance_tendsto_torusFourierGreenPairing
    d L mass hL hmass f g hf hg

end Pphi2Clean.Continuum
