import AImathPPhi2Clean.DimensionFreeWeightSummability
import Mathlib
noncomputable section
namespace Pphi2Clean.ArbitraryDim
class Parameters where
  dimension : ℕ
  dimension_pos : 0 < dimension
  energyOrder : ℝ
  energyOrder_gt : (dimension : ℝ) / 2 < energyOrder
  gap : ℝ
  gap_pos : 0 < gap
abbrev dimension [Parameters] : ℕ := Parameters.dimension
abbrev energyOrder [Parameters] : ℝ := Parameters.energyOrder
abbrev gap [Parameters] : ℝ := Parameters.gap
lemma gap_positive [Parameters] : 0 < gap := Parameters.gap_pos
lemma radial_summable {d : ℕ} (hd : 0 < d) (p : ℝ) (hp : (d : ℝ) < p) :
    Summable (fun k : Fin d → ℤ => (1 + ‖k‖) ^ (-p)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp0 : 0 ≤ p := le_of_lt (lt_trans hdR hp)
  have hq : 1 < p / (d : ℝ) := (lt_div_iff₀ hdR).mpr (by simpa using hp)
  apply Summable.of_nonneg_of_le
  · intro k
    exact Real.rpow_nonneg (by positivity) _
  · intro k
    exact DimensionFreeProbe.radial_weight_le_productWeight hd p hp0 k
  · exact DimensionFreeProbe.productWeight_summable _ hq d
variable [Parameters]
lemma energy_weight_summable :
    Summable (fun k : Fin dimension → ℤ => (1 + ‖k‖) ^ (-2 * energyOrder)) := by
  convert radial_summable Parameters.dimension_pos (2 * energyOrder) (by
    have h := Parameters.energyOrder_gt
    change (dimension : ℝ) / 2 < energyOrder at h
    linarith) using 1 <;> ring
lemma target_weight_summable :
    Summable (fun k : Fin dimension → ℤ => (1 + ‖k‖) ^ (-2 * (energyOrder + gap))) := by
  convert radial_summable Parameters.dimension_pos (2 * (energyOrder + gap)) (by
    have h := Parameters.energyOrder_gt
    change (dimension : ℝ) / 2 < energyOrder at h
    linarith [gap_positive]) using 1 <;> ring
lemma target_fourier_term_le_radius_factor (k : Fin dimension → ℤ) (R : ℕ)
    (hR : (R : ℝ) ≤ ‖k‖) :
    (1 + ‖k‖) ^ (-2 * (energyOrder + gap)) ≤
      (1 + (R : ℝ)) ^ (-(2 * gap)) * (1 + ‖k‖) ^ (-2 * energyOrder) := by
  have hb : 0 < 1 + ‖k‖ := by positivity
  have he : -2 * (energyOrder + gap) = (-(2 * gap)) + -2 * energyOrder := by ring
  rw [he, Real.rpow_add hb]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hb.le _)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith [gap_positive])
end Pphi2Clean.ArbitraryDim
