import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
import AImathPPhi2Clean.Periodic3DSobolevWeights

noncomputable section
namespace Pphi2Clean.Continuum

/-- The generic fixed signed-mode resolvent limit, explicitly instantiated in three dimensions. -/
theorem periodic3D_fixed_mode_mass_symbol_inv_tendsto
    (L mass : ℝ) (hmass : 0 < mass) (k : Periodic3DIndex) :
    Filter.Tendsto
      (fun n : ℕ =>
        (fixedVolumeMassSymbol 3 (n + 1) L mass
          (integerLatticeMode 3 (n + 1) k))⁻¹)
      Filter.atTop
      (nhds (torusMassSymbol 3 L mass k : ℂ)⁻¹) := by
  exact fixedVolumeMassSymbol_integerLatticeMode_inv_tendsto
    3 L mass hmass k

/-- At zero frequency the limiting massive denominator is exactly `mass^2`;
this handles the exceptional zero mode without a nonzero-frequency argument. -/
theorem periodic3D_zero_mode_mass_symbol_inv_tendsto
    (L mass : ℝ) (hmass : 0 < mass) :
    Filter.Tendsto
      (fun n : ℕ =>
        (fixedVolumeMassSymbol 3 (n + 1) L mass
          (integerLatticeMode 3 (n + 1) (0 : Periodic3DIndex)))⁻¹)
      Filter.atTop
      (nhds ((mass ^ 2 : ℂ)⁻¹)) := by
  simpa [torusMassSymbol] using
    periodic3D_fixed_mode_mass_symbol_inv_tendsto L mass hmass (0 : Periodic3DIndex)

end Pphi2Clean.Continuum
