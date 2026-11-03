import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
noncomputable section
open scoped BigOperators
def w (k : Fin 2 → ℤ) : ℝ := if k = 0 then 0 else ‖k‖ ^ (-4 : ℝ)
example : Summable w := by
  have h := EisensteinSeries.summable_one_div_norm_rpow (show (2 : ℝ) < 4 by norm_num)
  apply h.congr
  intro k
  by_cases hk : k = 0 <;> simp [w, hk]
