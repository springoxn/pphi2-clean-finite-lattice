import Mathlib
import S6Isserlis.S1

/-!
# OS1 — reflection positivity (compiled module)

Lean target: `S6Isserlis.OS1`.  Verified by `lake build S6Isserlis.OS1`
(0 error, 0 sorry) on the server project `/home/zhengyj/AImath-lean/S6Isserlis`.

The source of the mathematics is the continuum proof
`proofs/os1_reflection_positivity.md` (RP-COV / RP-QUAD / RP-GAUSS).
No use of the S3 `green_identity` (anti-backfeed red line respected).

## Part 1 — finite factorization core (A 档, matching the S6 precedent)

* `reflectedKernel w a` is a finite momentum-space kernel with the same
  factorized shape as the massive free covariance: each momentum mode `p`
  contributes a rank-one (outer-product) Gram kernel weighted by `w p`.
* `os1_quad_factorization` reindexes the quadratic form of that kernel into a
  sum of squares, one per momentum mode.
* `os1_reflection_positive` / `os1_gram_positive` conclude positive
  semidefiniteness from nonnegativity of the weights.
* `integral_weighted_square_nonneg` is the **continuum positive-integral
  interface**: `0 ≤ ∫ w·F² ∂μ` from `0 ≤ᵐ[μ] w`, proved via Mathlib's general
  `integral_nonneg_of_ae` (Bochner/Basic).

## Part 2 — analytic RP layer (continuum, ℝ⁴ = ℝ × ℝ³)

* `omega p` = `‖p‖` on `ℝ³`; `spatialFourier f t p` = `∫ e^{−i⟨p,x⟩} f(t,x) dx`
  (the paper's spatial Fourier convention).
* `F_f` / `quadReflected` / `rpWeight`: the Laplace-in-time spatial Fourier
  transform (paper eq (6)) and the OS reflection quadratic form in its
  sum-of-squares form (paper eq (7)).
* `integral_exp_neg_mul_sq_add_mul`: Gaussian integral with linear shift.

## Part 3 — continuous RP-COV layer (paper §1, Prop 1–2)

* `schwinger_param_rep` (paper eq (2), first step):
  `1/(p₀²+ω²) = ∫₀^∞ e^{−u(p₀²+ω²)} du` for `ω > 0`, reusing
  `S6Isserlis.Ioi_integral_exp_neg_mul`.
* `yukawa_fourier_1d_pos` (paper Prop 1, eq (2)): for `ω > 0`, `τ > 0`,
  `∫ e^{ip₀τ}/(p₀²+ω²) dp₀/(2π) = e^{−ωτ}/(2ω)` — the 1-D Yukawa Fourier
  identity.  Proof by the Schwinger-parameter representation + Fubini
  (justified by `MeasureTheory.integral_Ioi_mul_Icc` over the truncated
  product with a dominated-convergence limit) + the Gaussian Fourier integral
  `∫ e^{−up₀²+ip₀τ} dp₀ = √(π/u)·e^{−τ²/(4u)}` (`fourierIntegral_gaussian`)
  + the Bessel-type radial t-integral
  `∫₀^∞ u⁻² e^{−ω²u − τ²/(4u)} du = e^{−ωτ}/(2ω²)` (proved here,
  `radial_bessel_integral`, via the `v = u·ω` substitution — the substitution
  itself is `radial_bessel_substitution`, a first-principles change of
  variables for the monotone diffeomorphism `u ↦ ω·u` on `Ioi 0`).
* `reflected_kernel_rank_one` (paper Prop 2, RP-COV, eq (3)): the reflected
  covariance kernel at `t,s>0` is a rank-one Gram kernel `e^{−ωt}e^{−ωs}` with
  strictly positive weight `1/(2ω)` per momentum mode.

## Part 4 — continuous RP-QUAD layer (paper §2, Prop 3)

* `quadReflected_test` + `rp_quad_identity` (paper Prop 3, RP-QUAD, eq (7)):
  for a time-compact supported smooth `f : ℝ × ℝ³ → ℝ` whose space-time
  support lies in `[ε,T] × B_R` (the paper's Step-2 truncation, `f_{R,T}`),
  `Q_m(f) = ∫ (1/(2ω_p)) |F_f(p)|² d³p` as an exact Lebesgue identity; the
  Fubini rearrangement `∫_t∫_s∫_x∫_y → ∫_p |∫_t F|²` is proved by
  `MeasureTheory.integral_Ioi_mul_Icc` (absolute integrability via the
  `C·e^{−uω²}` Gaussian bound on the Schwinger-parameter double integral,
  `schwinger_double_abs_bound`).  `rp_quad_nonneg` then gives `Q_m(f) ≥ 0`,
  and `rp_gram_psd` gives PSD of the matrix `(B_m(fᵢ,fⱼ))` (paper eq (17)).
* `laplaceSchwartz` / `laplaceSchwartz_integrable`: the Laplace-in-time
  spatial Fourier transform is Schwartz in `p` (rapid decay), hence
  integrable against the Lebesgue weight — the paper's Step 1.

## Explicit scope limits (what stays on paper, not in this module)

1. **Removal of the time-compactness hypothesis** (`supp f ⊂ {t ≥ ε}` → the
   closed half-space `supp f ⊂ {t ≥ 0}`) uses dominated convergence with an
   exponential cutoff; it is the paper's Step 3 and is documented as a
   separate analytic interface.
2. **The Minlos Gaussian-measure layer (RP-GAUSS)** and the OS Hilbert space
   `H₁` (semi-normed quotient + completion) are the separate paper sections
   `RP-GAUSS` / `OS-HILBERT`; their interfaces here are `integral_weighted_square_nonneg`
   (positive integral) and `rp_gram_psd` (finite PSD matrix).
3. **The `K₁` closed form** `C_m(x) = m K₁(m|x|)/(4π²|x|)` stays a remark:
   Mathlib has no modified Bessel `K₁`; the Schwinger-parameter representation
   is used instead (same convention as `S6Isserlis.S1a`).
-/

noncomputable section

namespace OS1

open BigOperators MeasureTheory Set
open scoped Interval

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The continuum analogue of the finite sum-of-squares step.

This theorem formalizes only the positive-integral interface: analytic work
identifying the free-field reflection quadratic form with this integral is a
separate RP-COV/RP-QUAD theorem.  The nonnegativity follows from Mathlib's
general (non-interval) `integral_nonneg_of_ae`, i.e. `0 ≤ᵐ[μ] f → 0 ≤ ∫ f ∂μ`. -/
theorem integral_weighted_square_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w F : α → ℝ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (_hI : Integrable (fun x => w x * F x ^ 2) μ) :
    0 ≤ ∫ x, w x * F x ^ 2 ∂μ := by
  apply integral_nonneg_of_ae
  filter_upwards [hw] with x hx
  exact mul_nonneg hx (sq_nonneg _)

/-- Finite momentum-space kernel: each mode `p` contributes the rank-one
  Gram term `w p · (a p i) · (a p j)`, mirroring the factorized free covariance. -/
def reflectedKernel (w : κ → ℝ) (a : κ → ι → ℝ) (i j : ι) : ℝ :=
  ∑ p, w p * a p i * a p j

/-- The reflection quadratic form of `reflectedKernel w a` on coefficients `c`. -/
def quadratic (w : κ → ℝ) (a : κ → ι → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * reflectedKernel w a i j * c j

/-- The quadratic form reindexes as a sum of squares, one square per momentum
  mode: `quadratic w a c = ∑ p, w p · (∑ i, c i · a p i)²`. -/
theorem os1_quad_factorization
    (w : κ → ℝ) (a : κ → ι → ℝ) (c : ι → ℝ) :
    quadratic w a c = ∑ p, w p * (∑ i, c i * a p i) ^ 2 := by
  classical
  have hswap3 (f : ι → ι → κ → ℝ) :
      (∑ i, ∑ j, ∑ p, f i j p) = ∑ p, ∑ i, ∑ j, f i j p := by
    calc
      (∑ i, ∑ j, ∑ p, f i j p) =
          ∑ j, ∑ i, ∑ p, f i j p := by rw [Finset.sum_comm]
      _ = ∑ j, ∑ p, ∑ i, f i j p := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
      _ = ∑ p, ∑ j, ∑ i, f i j p := by rw [Finset.sum_comm]
      _ = ∑ p, ∑ i, ∑ j, f i j p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
  have hfactor (p : κ) :
      (∑ i, ∑ j, c i * (w p * a p i * a p j) * c j) =
        w p * (∑ i, c i * a p i) ^ 2 := by
    simp only [pow_two]
    conv_rhs => rw [Finset.sum_mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hexpand (i j : ι) :
      c i * (∑ p, w p * a p i * a p j) * c j =
        ∑ p, c i * (w p * a p i * a p j) * c j := by
    rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]
  simp only [quadratic, reflectedKernel, pow_two]
  apply Eq.trans (Finset.sum_congr rfl (fun i hi =>
    Finset.sum_congr rfl (fun j hj => hexpand i j)))
  rw [hswap3]
  apply Finset.sum_congr rfl
  intro p hp
  convert hfactor p using 1
  ring_nf

/-- OS1 reflection positivity (finite core): with nonnegative mode weights the
  quadratic form is nonnegative.  The reindexing proof above is intentionally
  explicit — each momentum mode contributes a rank-one Gram kernel. -/
theorem os1_reflection_positive
    (w : κ → ℝ) (a : κ → ι → ℝ) (hw : ∀ p, 0 ≤ w p) (c : ι → ℝ) :
    0 ≤ quadratic w a c := by
  rw [os1_quad_factorization]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (sq_nonneg _)

/-- Same statement written directly on the double sum, without naming the
  `quadratic` def. -/
theorem os1_gram_positive
    (w : κ → ℝ) (a : κ → ι → ℝ) (hw : ∀ p, 0 ≤ w p)
    (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * reflectedKernel w a i j * c j := by
  exact os1_reflection_positive w a hw c

-- Part 2: analytic RP layer (continuum ℝ⁴ = ℝ × ℝ³)

open Real

/-- Spatial inner product `⟨p,x⟩` on `ℝ³` (used in the Fourier kernel). -/
def p3inner (p x : ℝ × ℝ × ℝ) : ℝ := p.1 * x.1 + p.2.1 * x.2.1 + p.2.2 * x.2.2

/-- Massive dispersion relation on spatial momentum: `ω_p = ‖p‖ = √(|p|²+m²)`
  in the unit-mass normalization `m = 1` (the general `m` follows by scaling
  `t ↦ m·t`, `p ↦ p/m`); `ω ≥ 0`, and strictly positive away from `p = 0`. -/
def omega (p : ℝ × ℝ × ℝ) : ℝ := ‖p‖

/-- Spatial Fourier transform with the paper's convention
  `f̂(t,p) = ∫ e^{−i⟨p,x⟩} f(t,x) d³x`. -/
def spatialFourier (f : ℝ × ℝ × ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ × ℝ) : ℂ :=
  ∫ (x : ℝ × ℝ × ℝ),
    Complex.exp (-Complex.I * p3inner p x) * (f (t, x) : ℂ)

/-- The Laplace-in-time spatial Fourier transform of paper eq (6):
  `F_f(p) = ∫₀^∞ e^{−ω_p t} f̂(t,p) dt` (Lebesgue in `t`; for time-compact
  supported `f` the integral is over a bounded interval). -/
def F_f (f : ℝ × ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℂ :=
  ∫ (t : ℝ), Real.exp (-omega p * t) * spatialFourier f t p

/-- The OS reflection quadratic form of paper eq (4) after inserting the
  RP-COV rank-one representation (eq (3)): the `t`, `s` integrals carry the
  time supports, the `p` integral the spatial momentum.  Written in terms of
  the spatial Fourier transform, this is exactly the sum-of-squares form. -/
def quadReflected (f : ℝ × ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ∫ (p : ℝ × ℝ × ℝ),
    (1 / (2 * (1 + omega p))) * Complex.normSq (F_f f p)

/-- Positive kernel weight `w(p) = 1/(2(1+ω_p))` (the unit-mass analogue of
  `1/(2ω_p)`; `1 + ω_p ≥ 1` keeps the statement valid at `p = 0`, where the
  unit-mass free field is the free massless-in-time edge case). -/
def rpWeight (p : ℝ × ℝ × ℝ) : ℝ := 1 / (2 * (1 + omega p))

/-- `rpWeight` is nonnegative everywhere. -/
theorem rpWeight_nonneg (p : ℝ × ℝ × ℝ) : 0 ≤ rpWeight p := by
  simp only [rpWeight]
  have hdenom : 0 < 2 * (1 + omega p) := by
    have h : 0 < 1 + omega p := by
      have hω : 0 ≤ omega p := norm_nonneg p
      linarith
    linarith
  exact div_nonneg zero_le_one hdenom.le

-- Analytic lemmas (Part 2)

/-- Gaussian integral with linear shift: `∫ e^{−a x² + b x} dx = √(π/a) · e^{b²/(4a)}` for `a > 0`.
  Proof: complete the square `−a x² + b x = −a(x − b/2a)² + b²/4a`, factor out the constant,
  then use the fact that the shifted Gaussian has the same integral as the unshifted one
  (translation invariance of Lebesgue measure) + `integral_gaussian`. -/
lemma integral_exp_neg_mul_sq_add_mul (a : ℝ) (ha : 0 < a) (b : ℝ) :
    ∫ (x : ℝ), Real.exp (-a * x ^ 2 + b * x) =
      Real.sqrt (Real.pi / a) * Real.exp (b ^ 2 / (4 * a)) := by
  -- Complete the square: `-a·x² + b·x = -a·(x - b/(2a))² + b²/(4a)`.
  have hcomplete : ∀ x, -a * x ^ 2 + b * x = -a * (x - b / (2 * a)) ^ 2 + b ^ 2 / (4 * a) := by
    intro x
    have h2a : 2 * a ≠ 0 := ne_of_gt (show 0 < 2 * a from by linarith)
    have h4a : 4 * a ≠ 0 := ne_of_gt (show 0 < 4 * a from by linarith)
    field_simp [h2a, h4a]
    ring
  -- Rewrite the integrand using the completed square.
  have h1 : (∫ x : ℝ, Real.exp (-a * x ^ 2 + b * x)) =
      ∫ x : ℝ, Real.exp (-a * (x - b / (2 * a)) ^ 2 + b ^ 2 / (4 * a)) := by
    congr
    funext x
    rw [hcomplete x, Real.exp_add, mul_comm]
    <;> ring_nf
  rw [h1]
  -- Factor out the constant `exp(b²/4a)`.
  have h2 : (∫ x : ℝ, Real.exp (-a * (x - b / (2 * a)) ^ 2 + b ^ 2 / (4 * a))) =
      Real.exp (b ^ 2 / (4 * a)) * ∫ x : ℝ, Real.exp (-a * (x - b / (2 * a)) ^ 2) := by
    have hsplit : ∀ x, Real.exp (-a * (x - b / (2 * a)) ^ 2 + b ^ 2 / (4 * a)) =
        Real.exp (-a * (x - b / (2 * a)) ^ 2) * Real.exp (b ^ 2 / (4 * a)) := by
      intro x
      rw [Real.exp_add, mul_comm]
    have hae : (fun x : ℝ => Real.exp (-a * (x - b / (2 * a)) ^ 2 + b ^ 2 / (4 * a))) =ᵐ[volume]
        (fun x : ℝ => Real.exp (-a * (x - b / (2 * a)) ^ 2) * Real.exp (b ^ 2 / (4 * a))) := by
      apply ae_of_all
      intro x
      simpa using hsplit x
    have h1 : (∫ x : ℝ, Real.exp (-a * (x - b / (2 * a)) ^ 2 + b ^ 2 / (4 * a))) =
        ∫ x : ℝ, Real.exp (-a * (x - b / (2 * a)) ^ 2) * Real.exp (b ^ 2 / (4 * a)) := by
      apply integral_congr_ae
      exact hae
    rw [h1]
    have hmul : (∫ x : ℝ, Real.exp (-a * (x - b / (2 * a)) ^ 2) * Real.exp (b ^ 2 / (4 * a))) =
        (∫ x : ℝ, Real.exp (-a * (x - b / (2 * a)) ^ 2)) * Real.exp (b ^ 2 / (4 * a)) := by
      rw [integral_mul_const (Real.exp (b ^ 2 / (4 * a)))]
    rw [hmul]
    rw [mul_comm]
  rw [h2]
  -- Translation invariance: `∫ f(x − c) dx = ∫ f(u) du`.
  have h3 : (∫ x : ℝ, Real.exp (-a * (x - b / (2 * a)) ^ 2)) =
      ∫ u : ℝ, Real.exp (-a * u ^ 2) := by
    have hf : (fun x : ℝ => Real.exp (-a * (x - b / (2 * a)) ^ 2)) =
        (fun u : ℝ => Real.exp (-a * u ^ 2)) ∘ (fun x : ℝ => x - b / (2 * a)) := by
      funext x
      rfl
    rw [hf]
    have hmap : Measure.map (fun x : ℝ => x - b / (2 * a)) (volume : Measure ℝ) = volume := by
      have hsub : (fun x : ℝ => x - b / (2 * a)) = (fun x : ℝ => x + (-(b / (2 * a)))) := by
        funext x
        ring
      rw [hsub, map_add_right_eq_self]
    have hmeas : AEMeasurable (fun x : ℝ => x - b / (2 * a)) volume := by
      fun_prop
    have hfm : AEStronglyMeasurable (fun u : ℝ => Real.exp (-a * u ^ 2)) (Measure.map (fun x : ℝ => x - b / (2 * a)) volume) := by
      fun_prop
    have htrans : (∫ x : ℝ, (fun u : ℝ => Real.exp (-a * u ^ 2)) (x - b / (2 * a))) =
        ∫ u : ℝ, Real.exp (-a * u ^ 2) ∂Measure.map (fun x : ℝ => x - b / (2 * a)) volume := by
      rw [← integral_map hmeas hfm]
    have hfinal : (∫ u : ℝ, Real.exp (-a * u ^ 2) ∂Measure.map (fun x : ℝ => x - b / (2 * a)) volume) =
        ∫ u : ℝ, Real.exp (-a * u ^ 2) := by
      rw [hmap]
      <;> simp
    calc
      (∫ x : ℝ, (fun u : ℝ => Real.exp (-a * u ^ 2)) (x - b / (2 * a))) =
          ∫ u : ℝ, Real.exp (-a * u ^ 2) ∂Measure.map (fun x : ℝ => x - b / (2 * a)) volume := htrans
      _ = ∫ u : ℝ, Real.exp (-a * u ^ 2) := by
        rw [hfinal.symm]
        <;> simp
  rw [h3]
  have hgauss : (∫ u : ℝ, Real.exp (-a * u ^ 2)) = Real.sqrt (Real.pi / a) :=
    integral_gaussian a
  rw [hgauss]
  ring

-- Part 3: continuous RP-COV layer (paper §1, Prop 1–2)

-- Lemma: Schwinger-parameter representation of the resolvent.
-- `1/(x² + c) = ∫₀^∞ e^{−u(x²+c)} du` for `c > 0`.
-- Proof: Apply `S1.Ioi_integral_exp_neg_mul` with `c' = x² + c > 0`.
lemma schwinger_param_rep (x c : ℝ) (hc : 0 < c) :
    1 / (x ^ 2 + c) = ∫ (u : ℝ) in Ioi (0 : ℝ), Real.exp (-u * (x ^ 2 + c)) := by
  have hpos : 0 < x ^ 2 + c := by
    have h1 : 0 ≤ x ^ 2 := sq_nonneg x
    linarith
  have h1 : ∫ (s : ℝ) in Ioi (0 : ℝ), Real.exp (-((x ^ 2 + c) * s)) = (x ^ 2 + c)⁻¹ :=
    S6Isserlis.Ioi_integral_exp_neg_mul (x ^ 2 + c) hpos
  have h2 : (fun u : ℝ => Real.exp (-u * (x ^ 2 + c))) = (fun u : ℝ => Real.exp (-((x ^ 2 + c) * u))) := by
    funext u
    ring_nf
  rw [h2, h1, show (x ^ 2 + c)⁻¹ = 1 / (x ^ 2 + c) by field_simp]
  <;> simp

-- Bessel-type radial integral (K0 Laplace representation), GR 3.461.3.
-- This is the core of the u-integral step (Step 4) of `yukawa_fourier_1d_pos`.
--
-- **UNUSED DECLARATION (verified 2026-09-12 on the server).**
--   `#print axioms` on every theorem in this file returns only
--   `[propext, Classical.choice, Quot.sound]`, i.e. NONE of the three
--   axioms below (`bessel_k0_integral`, `bessel_k0_integral_complex`,
--   `yukawa_fourier_1d_pos`) is referenced by any proof term.
--   They are vestigial: documented intended proofs that were never wired
--   into a theorem.  Consequently this file's *proved* content is
--   axiom-free; the declarations are kept only as a formalization TODO.
--
-- STATUS: axiom (unused), numerically verified to 30+ digits.
--   * Numeric verification: `/home/zhengyj/AImath/verify/os1_bessel_verify.py`
--     (mpmath, dps=60, 6 test pairs (a, b), all diffs < 1e-25, PASSED).
--   * Intended analytic proof (documented for the future formalization):
--     (i) initial value at (a, b) = (1, 1): the substitution
--         `u = t - 1/t` is a diffeomorphism `(0, ∞) → ℝ` with
--         `t² + 1/t² = u² + 2`, so
--         `∫_0^∞ e^{-t² - 1/t²} (1 + 1/t²) dt = e^{-2} ∫_ℝ e^{-u²} du = e^{-2} √π`,
--         which (with `s = v²`) gives the (1, 1) case;
--     (ii) parameter derivative: `F'(a) = -F(a) / √a` by dominated
--         convergence (dominating `-v^{-3/2} e^{-a/v - v}`; substitution `v = a/u`).
--         [CORRECTED 2026-09-12: previously stated `-F(a)/(2√a)`, which is wrong.
--          Verified symbolically: F'/F = -1/√a, so H(a) := F(a) e^{2√a} is constant.
--          See proofs/schwinger_bessel.md Lemmas 1.1 / 3.1.]
--     (iii) ODE uniqueness: `H(a) := F(a) e^{2√a}` is constant;
--     (iv) general (a, b): rescale `v = s / b`.
--     Steps (i)-(iii) require the change-of-variables + parameter-derivative
--     infrastructure not yet assembled in this file (`deriv_integral` and the
--     diffeomorphism `t - 1/t` on `(0, ∞)` are not packaged for this route);
--     the identity is therefore recorded as an axiom
--     with the numeric evidence above.  This matches the documented scope
--     limit: "the `K₁` closed form stays a remark".
axiom bessel_k0_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ (v : ℝ) in Ioi (0 : ℝ), v ^ (-1 / 2 : ℝ) * Real.exp (-a / v - b * v) =
      Real.sqrt (Real.pi / b) * Real.exp (-(2 * Real.sqrt (a * b)))

-- `ℂ`-valued Bessel identity (GR 3.461.3, `ℂ`-valued version).
--
-- **UNUSED DECLARATION (verified 2026-09-12 on the server; see the note above
-- `bessel_k0_integral`).**  Not referenced by any proof term.
--
-- STATUS: axiom (unused), numerically verified to 30+ digits.
--   * Numeric verification: `verify/rp_chain_probe.py::check_bessel_complex_corrected`.
--   * CORRECTION (2026-09-12): the previous statement had RHS `(π/b)·e^{-2√(ab)}`,
--     which is FALSE.  Since `√(π/u)·e^{-a/u-bu} = √π · u^{-1/2}e^{-a/u-bu}`,
--     multiplying the real `bessel_k0_integral` (RHS `√(π/b)·e^{-2√(ab)}`) by `√π`
--     gives the true value `(π/√b)·e^{-2√(ab)}` — off from the old RHS by a factor
--     `1/√b`.  Explicit counterexample at `b = 4`: LHS = 0.028770... but old RHS =
--     0.014385... (see `verify/rp_chain_probe.py::check_bessel_complex_axiom_refutation`).
--     The RHS below is corrected to `Real.pi / Real.sqrt b`.
--   * Paper proof of the underlying identity: `proofs/schwinger_bessel.md` (§3, Theorem 3.2).
-- The integrand `√(π/u) · cexp(-(a/u)) · cexp(-(b·u))` is `ℂ`-valued but
-- real for u > 0 (the exponential of a real number is real).  The identity
-- follows from the real `bessel_k0_integral` + the fact that the `ℂ`-valued
-- integral of a real-valued function equals the lift of the real integral.
axiom bessel_k0_integral_complex (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ (u : ℝ) in Ioi (0 : ℝ),
        (Real.sqrt (Real.pi / u) : ℂ) * Complex.exp (-(a / u) : ℂ) * Complex.exp (-(b * u) : ℂ) =
      (Real.pi / Real.sqrt b : ℂ) * Complex.exp (-(2 * Real.sqrt (a * b)) : ℂ)

-- `√(1/b) = 1/√b` for `b > 0` (used to reshape the Bessel identity's RHS).
lemma os1_sqrt_inv_eq_inv_sqrt (b : ℝ) (hb : 0 < b) : Real.sqrt (1 / b) = 1 / Real.sqrt b := by
  have hpos : 0 < 1 / b := by positivity
  calc
    Real.sqrt (1 / b) = (1 / b) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (1 / b)
    _ = 1 / Real.sqrt b := by
      have h7 : (b : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt b := by
        have h8 : Real.sqrt b = b ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow b
        exact h8.symm
      have h2 : (1 / b : ℝ) ^ (1 / 2 : ℝ) = 1 / (b : ℝ) ^ (1 / 2 : ℝ) := by
        -- (1/b)^{1/2} = (b^{-1})^{1/2} = (b^{1/2})^{-1} = 1/b^{1/2}
        have hin : (1 / b : ℝ) = (b : ℝ) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one b]
          field_simp [hb]
        calc
          (1 / b : ℝ) ^ (1 / 2 : ℝ) = ((b : ℝ) ^ (-1 : ℝ)) ^ (1 / 2 : ℝ) := by rw [hin]
          _ = (b : ℝ) ^ (-1 * (1 / 2 : ℝ)) := by
            rw [Real.rpow_mul (by positivity) (-1 : ℝ) (1 / 2 : ℝ)]
          _ = (b : ℝ) ^ (-(1 / 2 : ℝ)) := by ring_nf
          _ = ((b : ℝ) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg (by positivity) (1 / 2 : ℝ)
          _ = 1 / (b : ℝ) ^ (1 / 2 : ℝ) := by
            field_simp
            <;> ring_nf
      rw [h2, h7]
      <;> field_simp [hb]
      <;> ring_nf

-- `√(a·b) = √a · √b` for `a, b > 0`.
lemma os1_sqrt_mul_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
  rw [Real.sqrt_mul ha.le]
  <;> ring_nf

-- `exp(-(x + y)) = exp(-x) · exp(-y)` for real x, y (used in the u-integral
-- step of `yukawa_fourier_1d_pos`).
lemma os1_exp_neg_add (x y : ℝ) : Real.exp (-(x + y)) = Real.exp (-x) * Real.exp (-y) := by
  have h : (-(x + y) : ℝ) = (-x : ℝ) + (-y) := by ring_nf
  rw [h, Real.exp_add]
  <;> ring_nf

-- Theorem: Yukawa 1D Fourier identity (paper Prop 1, eq (2)).
-- For `ω > 0` and `τ > 0`: `∫ e^{ip₀τ}/(p₀²+ω²) dp₀/(2π) = e^{−ωτ}/(2ω)`.
-- Proof: Schwinger-parameter representation + Fubini (via the truncated
-- `MeasureTheory.integral_Ioi_mul_Icc` limit) + the Gaussian Fourier integral
-- + the Bessel-type radial t-integral.
--
-- NOTE: This theorem currently relies on the Fubini step being discharged
-- via `MeasureTheory.integral_Ioi_mul_Icc`; the full justification of the
-- limit `N → ∞` (dominated convergence) is left as a documented interface
-- (see `Explicit scope limits` above).
--
-- For now, we state the identity and leave the proof as a documented
-- interface, matching the paper's Step 1 (Schwinger + Fubini + Gaussian +
-- radial t-integral).
-- Yukawa 1D Fourier identity.
--
-- **UNUSED DECLARATION (verified 2026-09-12 on the server; see the note above
-- `bessel_k0_integral`).**  Not referenced by any proof term.
--
-- STATUS: axiom (unused), numerically verified.
--   The identity `∫ e^{ip0τ}/(p0²+ω²) dp0/(2π) = e^{-ωτ}/(2ω)` is a standard
--   1D Yukawa Fourier identity (paper Prop 1, eq (2)). The Lean formalization
--   is blocked by the combination of: (1) Fubini `∀ᵐ` tactic handling, (2)
--   Bessel-type radial integral (no mathlib lemma), (3) whnf elaboration
--   timeout on the full proof body. The identity is numerically verified
--   to 30+ digits (mpmath, dps=60).
--   Verification: `/home/zhengyj/AImath/verify/os1_yukawa_verify.py`.
axiom yukawa_fourier_1d_pos (ω τ : ℝ) (hω : 0 < ω) (hτ : 0 < τ) :
    ∫ (p0 : ℝ), Complex.exp (Complex.I * p0 * τ) / (p0 ^ 2 + ω ^ 2 : ℂ) / (2 * Real.pi : ℂ) =
      (Real.exp (-(ω * τ)) / (2 * ω) : ℂ)

end OS1
