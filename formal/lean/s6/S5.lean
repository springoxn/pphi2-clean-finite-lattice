import S6Isserlis.OS1

noncomputable section

open scoped BigOperators
open MeasureTheory
open OS1

namespace Schwinger

/-- **OS0 two-point reflection positivity** (paper `thm:rpquad`, quadratic level): the
reflected quadratic form is nonnegative, its integrand being a nonnegative weight
(`rpWeight`, via `rpWeight_nonneg`) times a squared modulus (`Complex.normSq`). -/
theorem quadReflected_nonneg (f : ℝ × ℝ × ℝ × ℝ → ℝ) : 0 ≤ quadReflected f := by
  show 0 ≤ ∫ p : ℝ × ℝ × ℝ, rpWeight p * Complex.normSq (F_f f p)
  apply integral_nonneg_of_ae
  filter_upwards with p
  exact mul_nonneg (rpWeight_nonneg p) (Complex.normSq_nonneg _)

end Schwinger
