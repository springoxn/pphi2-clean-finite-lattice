import AImathPPhi2Clean.Periodic3DSobolevWeights

namespace Pphi2Clean.Continuum

theorem periodic3DHminusThreeWeight_le_hminusTwo (k : Periodic3DIndex) :
    periodic3DHminusThreeWeight k ≤ periodic3DHminusTwoWeight k := by
  unfold periodic3DHminusThreeWeight periodic3DHminusTwoWeight periodic3DSobolevWeight
  unfold fs4SobolevWeight
  have hmax : 0 ≤ max ‖(fs4SplitIndex (periodic3DExtend k)).1‖
      ‖(fs4SplitIndex (periodic3DExtend k)).2‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hbase : 1 ≤ 1 + max ‖(fs4SplitIndex (periodic3DExtend k)).1‖
      ‖(fs4SplitIndex (periodic3DExtend k)).2‖ := by linarith
  have hexp : -2 * (3 : ℝ) ≤ -2 * (2 : ℝ) := by norm_num
  exact Real.rpow_le_rpow_of_exponent_le hbase hexp

end Pphi2Clean.Continuum
