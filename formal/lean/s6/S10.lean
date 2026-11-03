import Mathlib
import S6Isserlis.S1a

/-!
# S10 — OS4: derivatives of the Gaussian factor `exp(-r²/(4t))`

Paper `lem:param-deriv` (eq:gaussianderiv): the `r`-derivatives of the Gaussian
`g_t(r) = exp(-r²/(4t))` have the form
`∂_r^k g_t(r) = g_t(r) * Σ_{j≤k} c_{k,j} r^j t^{-(k+j)/2}`.
This module records the exponential-prefactor identity on which the general
induction rests, together with the explicit low-order cases `k = 1, 2` anchoring it.
-/

noncomputable section

open scoped Topology

namespace OS4

/-- The Gaussian factor `g_t(r) = exp(-r²/(4t))` of the Schwinger parametrisation. -/
def gauss (t r : ℝ) : ℝ := Real.exp (-(r ^ 2) / (4 * t))

/-- `∂_r exp(-r²/(4t)) = -(r/(2t)) exp(-r²/(4t))`; the exponential prefactor is
preserved by differentiation (paper eq:gaussianderiv, the induction step). -/
lemma hasDerivAt_gaussExp (t r : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / (4 * t)))
      (-(r / (2 * t)) * Real.exp (-(r ^ 2) / (4 * t))) r := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h2 : HasDerivAt (fun x : ℝ => -(x ^ 2)) (-(2 * r)) r := h1.neg
  have h3 : HasDerivAt (fun x : ℝ => -(x ^ 2) / (4 * t)) (-(2 * r) / (4 * t)) r :=
    h2.div_const (4 * t)
  have h4 : -(2 * r) / (4 * t) = -(r / (2 * t)) := by
    field_simp; ring
  rw [h4] at h3
  have h5 := h3.exp
  have hval : Real.exp (-(r ^ 2) / (4 * t)) * (-(r / (2 * t)))
      = -(r / (2 * t)) * Real.exp (-(r ^ 2) / (4 * t)) := by ring
  rw [hval] at h5
  exact h5

/-- **eq:gaussianderiv, k = 1**. -/
theorem deriv_gauss (t r : ℝ) (ht : t ≠ 0) :
    deriv (gauss t) r = -(r / (2 * t)) * gauss t r := by
  change deriv (fun x : ℝ => Real.exp (-(x ^ 2) / (4 * t))) r
      = -(r / (2 * t)) * Real.exp (-(r ^ 2) / (4 * t))
  exact (hasDerivAt_gaussExp t r ht).deriv

/-- **eq:gaussianderiv, k = 2**, in the explicit form
`∂_r² exp(-r²/(4t)) = ((r² - 2t)/(4t²)) exp(-r²/(4t))`. -/
theorem deriv2_gauss (t r : ℝ) (ht : t ≠ 0) :
    deriv (deriv (gauss t)) r = ((r ^ 2 - 2 * t) / (4 * t ^ 2)) * gauss t r := by
  have hfun : deriv (gauss t) = fun x => -(x / (2 * t)) * gauss t x :=
    funext fun x => deriv_gauss t x ht
  rw [hfun]
  have hg : HasDerivAt (gauss t) (-(r / (2 * t)) * gauss t r) r := by
    change HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / (4 * t)))
      (-(r / (2 * t)) * Real.exp (-(r ^ 2) / (4 * t))) r
    exact hasDerivAt_gaussExp t r ht
  have hlin : HasDerivAt (fun x : ℝ => -(x / (2 * t))) (-(1 / (2 * t))) r := by
    have h2 : HasDerivAt (fun x : ℝ => x / (2 * t)) (1 / (2 * t)) r :=
      (hasDerivAt_id r).div_const (2 * t)
    exact h2.neg
  have hprod : HasDerivAt (fun x : ℝ => -(x / (2 * t)) * gauss t x)
      (-(1 / (2 * t)) * gauss t r + -(r / (2 * t)) * (-(r / (2 * t)) * gauss t r)) r :=
    hlin.mul hg
  rw [hprod.deriv]
  have hval : -(1 / (2 * t)) * gauss t r + -(r / (2 * t)) * (-(r / (2 * t)) * gauss t r)
      = ((r ^ 2 - 2 * t) / (4 * t ^ 2)) * gauss t r := by
    field_simp; ring
  rw [hval]

end OS4
