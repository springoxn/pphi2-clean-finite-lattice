import AImathPPhi2Clean.Periodic3DModePairing
import AImathPPhi2Clean.FiniteFourierCoordinateConvergence

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.UpstreamLattice

def periodic3DFourierTestFamily {m : ℕ} (L : ℝ) (hL : 0 < L)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    Fin m → BoundedContinuousFunction (Fin 3 → ℝ) ℝ :=
  periodicFourierTestFamily 3 m L hL modes useSine

theorem periodic3DFourierTestFamily_covariance_tendsto
    {m : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) (i j : Fin m) :
    Filter.Tendsto
      (fixedVolumeCovarianceInner 3 L mass hL hmass
        (periodic3DFourierTestFamily L hL modes useSine i)
        (periodic3DFourierTestFamily L hL modes useSine j))
      Filter.atTop
      (nhds (periodicResolventCovarianceMatrix 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine) i j)) := by
  change Filter.Tendsto
    (fixedVolumeCovarianceInner 3 L mass hL hmass
      (periodicFourierTestFamily 3 m L hL modes useSine i)
      (periodicFourierTestFamily 3 m L hL modes useSine j))
    Filter.atTop
    (nhds (periodicResolventCovarianceMatrix 3 m L mass hmass
      (periodicFourierTestFamily 3 m L hL modes useSine) i j))
  have hlim := fixedVolumeCovarianceInner_tendsto_periodicMassiveResolvent
    3 L mass hL hmass
    (periodicFourierTestFamily 3 m L hL modes useSine i)
    (periodicFourierTestFamily 3 m L hL modes useSine j)
    (periodicFourierTestFamily_isFlatTorusPeriodic 3 m L hL modes useSine i)
    (periodicFourierTestFamily_isFlatTorusPeriodic 3 m L hL modes useSine j)
  have hpair :
      (torusFourierGreenPairing 3 L mass
        (periodicFourierTestFamily 3 m L hL modes useSine i)
        (periodicFourierTestFamily 3 m L hL modes useSine j)).re =
      periodicResolventCovarianceMatrix 3 m L mass hmass
        (periodicFourierTestFamily 3 m L hL modes useSine) i j := by
    unfold periodicResolventCovarianceMatrix
    rw [← torusFourierGreenPairing_eq_physicalTorusResolventPairing 3 L mass hL hmass]
  have hphysical :
      (physicalTorusResolventPairing 3 L mass hmass
        (periodicFourierTestFamily 3 m L hL modes useSine i)
        (periodicFourierTestFamily 3 m L hL modes useSine j)).re =
      periodicResolventCovarianceMatrix 3 m L mass hmass
        (periodicFourierTestFamily 3 m L hL modes useSine) i j := by
    rw [← torusFourierGreenPairing_eq_physicalTorusResolventPairing 3 L mass hL hmass]
    exact hpair
  rw [← hphysical]
  exact hlim

theorem periodic3DFourierTestFamily_finiteMeasure_tendsto
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (modes : Fin m → Periodic3DIndex) (useSine : Fin m → Bool) :
    Filter.Tendsto
      (fun n : ℕ => let N := n + 1; letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        physicalFamilyEvalProbabilityMeasure 3 N m (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
          (periodic3DFourierTestFamily L hL modes useSine))
      Filter.atTop
      (nhds (periodicResolventTargetProbabilityMeasure 3 m L mass hmass
        (periodic3DFourierTestFamily L hL modes useSine))) := by
  simpa [periodic3DFourierTestFamily] using
    physicalPeriodicFourierFamilyProbabilityMeasure_fixedVolume_tendsto
      3 m L mass hL hmass modes useSine

end Pphi2Clean.Continuum
