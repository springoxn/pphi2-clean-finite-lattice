import Mathlib

/-!
# S6 — Isserlis 4-point moment (first Lean formalization target)

Source of truth for the mathematics: `verify/schwinger.py::check_isserlis_4pt`
(lemma [L15]) and the roadmap `formal/lean/schwinger.md` §4 (A 档 = mgf definition).

Goal (A 档): for a 0-mean Gaussian on `Fin 4 → ℝ` with covariance `Sig` (symmetric),
the fourth mixed moment equals the sum over the three perfect matchings of
`{1,2,3,4}`.

    E[X₁X₂X₃X₄] = Sig₁₂·Sig₃₄ + Sig₁₃·Sig₂₄ + Sig₁₄·Sig₂₃

Statement: `fourthMoment` is defined as the 4-th Fréchet derivative at `0` of the
mgf  `M(t) = exp(½ · tᵀSigt)`, applied to the four coordinate directions.  The proof
is the task of the adversarial loop (decomposer → prover → critic); this file pins
down the precise statement so compile errors can be ground out mechanically.

Mathlib coverage notes (from `formal/lean/schwinger.md` §4):
  * `iteratedFDeriv`, `ContinuousMultilinearMap`, `Real.exp`, `Matrix.mulVec`,
    `Matrix.dotProduct`, `Matrix.IsSymm` — all in Mathlib.
  * **GAP-D / missing combinatorics**: no ready-made "fourth derivative of a
    composition = Bell/Faa-di-Bruno sum" lemma; the n=4 case must be assembled by
    hand (finite `Finset` enumeration + `ring_nf`).
-/

noncomputable section

open scoped BigOperators Matrix

namespace S6

abbrev E := Fin 4 → ℝ

/-- The quadratic form `t ↦ ½ · tᵀSigt`, expanded as `½ · ∑ᵢⱼ tᵢ·Sigᵢⱼ·tⱼ`. -/
def quadForm (Sig : Matrix (Fin 4) (Fin 4) ℝ) (t : E) : ℝ :=
  (1 / 2 : ℝ) * (∑ i : Fin 4, ∑ j : Fin 4, t i * Sig i j * t j)

/-- mgf of a 0-mean Gaussian with covariance `Sig`: `M(t) = exp(quadForm Sig t)`. -/
def mgf (Sig : Matrix (Fin 4) (Fin 4) ℝ) (t : E) : ℝ :=
  Real.exp (quadForm Sig t)

/-- Fourth mixed moment, mgf-definition:
    `E[X₁X₂X₃X₄] := M⁗(0)(e₁,e₂,e₃,e₄)` where `eᵢ = Pi.single i 1`. -/
def fourthMoment (Sig : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (iteratedFDeriv ℝ 4 (mgf Sig) 0) (fun i : Fin 4 => Pi.single i 1)

/-- The right-hand side of Isserlis: sum over the three perfect matchings. -/
def isserlisRHS (Sig : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Sig 0 1 * Sig 2 3 + Sig 0 2 * Sig 1 3 + Sig 0 3 * Sig 1 2

/-! ### Smoothness and derivative support for `quadForm` -/

/-- `t ↦ quadForm Sig t` is smooth. -/
lemma contDiff_quadForm (Sig : Matrix (Fin 4) (Fin 4) ℝ) :
    ContDiff ℝ ⊤ (fun t : E => quadForm Sig t) := by
  unfold quadForm
  have hsum : ContDiff ℝ ⊤
      (fun t : E => ∑ i : Fin 4, ∑ j : Fin 4, t i * Sig i j * t j) := by
    apply ContDiff.sum
    intro i _hi
    apply ContDiff.sum
    intro j _hj
    have hpi : ContDiff ℝ ⊤ (fun t : E => t i) :=
      (ContinuousLinearMap.proj i : E →L[ℝ] ℝ).contDiff
    have hpj : ContDiff ℝ ⊤ (fun t : E => t j) :=
      (ContinuousLinearMap.proj j : E →L[ℝ] ℝ).contDiff
    exact (hpi.mul contDiff_const).mul hpj
  exact (contDiff_const : ContDiff ℝ ⊤ (fun _ : E => (1 / 2 : ℝ))).mul hsum

/-- Any fixed-order `iteratedFDeriv` of the smooth function `quadForm` is differentiable. -/
lemma differentiableAt_iteratedFDeriv_quadForm (Sig : Matrix (Fin 4) (Fin 4) ℝ) (m : ℕ) (x : E) :
    DifferentiableAt ℝ
      (fun y : E => iteratedFDeriv ℝ m (fun t : E => quadForm Sig t) y) x := by
  exact (contDiff_quadForm Sig).contDiffAt.differentiableAt_iteratedFDeriv (m := m) (by
    simp)

/-- The `fderiv` of a coordinate projection is the projection itself. -/
lemma fderiv_proj_apply (i : Fin 4) (x : E) :
    fderiv ℝ (fun t : E => t i) x = (ContinuousLinearMap.proj i : E →L[ℝ] ℝ) := by
  exact (ContinuousLinearMap.proj i : E →L[ℝ] ℝ).hasFDerivAt.fderiv

/-- First derivative of the monomial `t ↦ tᵢ·c·tⱼ`. -/
@[simp]
lemma mono_fderiv_apply (c : ℝ) (i j : Fin 4) (x w : E) :
    fderiv ℝ (fun t : E => t i * c * t j) x w = x i * c * w j + w i * c * x j := by
  have hpoint : (fun t : E => t i * c * t j) =
      (fun t : E => t i * c) * (fun t : E => t j) := by
    funext t
    rfl
  rw [hpoint]
  rw [fderiv_mul (by fun_prop) (by fun_prop)]
  have hf : fderiv ℝ (fun t : E => t i * c) x = (c • (ContinuousLinearMap.proj i : E →L[ℝ] ℝ)) := by
    rw [fderiv_mul_const (by fun_prop)]
    rw [fderiv_proj_apply]
  have hg : fderiv ℝ (fun t : E => t j) x = (ContinuousLinearMap.proj j : E →L[ℝ] ℝ) := by
    exact fderiv_proj_apply j x
  rw [hf, hg]
  simp
  ring

/-- Derivative of the linear summand `y ↦ yᵢ·ca + cb·yⱼ`. -/
@[simp]
lemma lin_term_fderiv_apply (ca cb : ℝ) (i j : Fin 4) (x v : E) :
    fderiv ℝ (fun y : E => y i * ca + cb * y j) x v = v i * ca + cb * v j := by
  have hpoint : (fun y : E => y i * ca + cb * y j) =
      (fun y : E => y i * ca) + (fun y : E => cb * y j) := by
    funext y
    rfl
  rw [hpoint]
  rw [fderiv_add (by fun_prop) (by fun_prop)]
  have h1 : fderiv ℝ (fun y : E => y i * ca) x = (ca • (ContinuousLinearMap.proj i : E →L[ℝ] ℝ)) := by
    rw [fderiv_mul_const (by fun_prop)]
    rw [fderiv_proj_apply]
  have h2 : fderiv ℝ (fun y : E => cb * y j) x = (cb • (ContinuousLinearMap.proj j : E →L[ℝ] ℝ)) := by
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_proj_apply]
  rw [h1, h2]
  simp
  ring

/-- Derivative of `y ↦ (yᵢ·ca)·cst + cb·yⱼ` (with a constant right factor). -/
@[simp]
lemma mono_lin_fderiv_apply (ca cst cb : ℝ) (i j : Fin 4) (x v : E) :
    fderiv ℝ (fun y : E => (y i * ca) * cst + cb * y j) x v = (v i * ca) * cst + cb * v j := by
  rw [show (fun y : E => (y i * ca) * cst + cb * y j) =
      (fun y : E => y i * (ca * cst) + cb * y j) by
    funext y
    ring]
  rw [lin_term_fderiv_apply]
  ring

/-- Application of a finite sum of continuous linear maps commutes with the sum. -/
@[simp]
lemma clm_sum_apply (v : E) (f : Fin 4 → E →L[ℝ] ℝ) :
    (∑ i : Fin 4, f i) v = ∑ i : Fin 4, (f i) v := by
  have hrec : ∀ s : Finset (Fin 4), (∑ i ∈ s, f i) v = ∑ i ∈ s, (f i) v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s has ih =>
        simpa [Finset.sum_insert has, ih]
  simpa using hrec (Finset.univ : Finset (Fin 4))

/-- `fderiv` of a double `Finset.sum` of functions is the double sum of `fderiv`s. -/
lemma fderiv_double_sum_apply {F : Fin 4 → Fin 4 → E → ℝ} (x : E)
    (hF : ∀ a b : Fin 4, DifferentiableAt ℝ (fun y : E => F a b y) x) :
    fderiv ℝ (fun y : E => ∑ a : Fin 4, ∑ b : Fin 4, F a b y) x =
      ∑ a : Fin 4, ∑ b : Fin 4, fderiv ℝ (fun y : E => F a b y) x := by
  have hc1 : (fun y : E => ∑ a : Fin 4, ∑ b : Fin 4, F a b y) =
      (∑ a : Fin 4, (fun y : E => ∑ b : Fin 4, F a b y)) := by
    funext y
    simp [Finset.sum_apply]
  rw [hc1]
  rw [fderiv_sum (u := (Finset.univ : Finset (Fin 4)))
    (A := fun a : Fin 4 => (fun y : E => ∑ b : Fin 4, F a b y))
    (h := by
      intro i hi
      have hf : (fun y : E => ∑ b : Fin 4, F i b y) = (∑ b : Fin 4, (fun y : E => F i b y)) := by
        funext y
        simp [Finset.sum_apply]
      rw [hf]
      exact DifferentiableAt.sum (u := (Finset.univ : Finset (Fin 4)))
        (A := fun b : Fin 4 => (fun y : E => F i b y)) (fun j hj => hF i j))]
  apply Finset.sum_congr rfl
  intro a ha
  have hc2 : (fun y : E => ∑ b : Fin 4, F a b y) = (∑ b : Fin 4, (fun y : E => F a b y)) := by
    funext y
    simp [Finset.sum_apply]
  rw [hc2]
  rw [fderiv_sum (u := (Finset.univ : Finset (Fin 4)))
    (A := fun b : Fin 4 => (fun y : E => F a b y))
    (h := by intro j hj; exact hF a j)]

/-- First derivative of the quadratic form along a direction. -/
lemma quadForm_fderiv_apply (Sig : Matrix (Fin 4) (Fin 4) ℝ) (x w : E) :
    fderiv ℝ (fun t : E => quadForm Sig t) x w =
      (1/2) * (∑ i : Fin 4, ∑ j : Fin 4, (x i * Sig i j * w j + w i * Sig i j * x j)) := by
  unfold quadForm
  have hD : DifferentiableAt ℝ
      (fun t : E => ∑ i : Fin 4, ∑ j : Fin 4, t i * Sig i j * t j) x := by
    fun_prop
  rw [fderiv_const_mul hD]
  simp only [smul_apply, smul_eq_mul]
  have hdsum := fderiv_double_sum_apply x
    (F := fun a b : Fin 4 => (fun t : E => t a * Sig a b * t b))
    (by intro a b; fun_prop)
  rw [hdsum]
  simp only [clm_sum_apply]
  simp [mono_fderiv_apply]

/-- Second iterated derivative of `quadForm`: it is the constant bilinear form
    `(a, b) ↦ ½·Σᵢⱼ (aᵢ·Sigᵢⱼ·bⱼ + bᵢ·Sigᵢⱼ·aⱼ)` (independent of the base point `x`). -/
lemma quadForm_iteratedFDeriv_two (Sig : Matrix (Fin 4) (Fin 4) ℝ) (x : E) (m : Fin 2 → E) :
    (iteratedFDeriv ℝ 2 (fun t : E => quadForm Sig t) x) m =
      (1/2) * (∑ a : Fin 4, ∑ b : Fin 4,
        (m 0 a * Sig a b * m 1 b + m 1 a * Sig a b * m 0 b)) := by
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
    (f := fun t : E => quadForm Sig t) (differentiableAt_iteratedFDeriv_quadForm Sig 1 x)]
  simp only [iteratedFDeriv_one_apply]
  have htail : (Fin.tail m) 0 = m 1 := rfl
  rw [htail]
  have hfun : (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1)) =
      (fun y : E => (1/2) * (∑ a : Fin 4, ∑ b : Fin 4,
        (y a * Sig a b * (m 1) b + (m 1) a * Sig a b * y b))) := by
    funext y
    rw [quadForm_fderiv_apply Sig y (m 1)]
  rw [hfun]
  have hD : DifferentiableAt ℝ
      (fun y : E => ∑ a : Fin 4, ∑ b : Fin 4,
        (y a * Sig a b * (m 1) b + (m 1) a * Sig a b * y b)) x := by
    fun_prop
  rw [fderiv_const_mul hD]
  simp only [smul_apply, smul_eq_mul]
  have hdsum := fderiv_double_sum_apply x
    (F := fun a b : Fin 4 => (fun y : E =>
      (y a * Sig a b * (m 1) b + (m 1) a * Sig a b * y b)))
    (by intro a b; fun_prop)
  rw [hdsum]
  simp only [clm_sum_apply]
  simp only [mono_lin_fderiv_apply]

/-! ### Helper lemmas (statements pinned; proven below) -/

/-- `quadForm` is quadratic: the mixed second partial in directions `eᵢ,eⱼ` at `0`
    equals the matrix entry `Sigᵢⱼ` (symmetry is what removes the ½). -/
lemma quadForm_second_partial
    (Sig : Matrix (Fin 4) (Fin 4) ℝ) (hSymm : Sig.IsSymm) (i j : Fin 4) :
    (iteratedFDeriv ℝ 2 (fun t : E => quadForm Sig t) 0)
        (fun k : Fin 2 => if k = 0 then Pi.single i (1 : ℝ) else Pi.single j (1 : ℝ))
          = Sig i j := by
  let m : Fin 2 → E := fun k : Fin 2 => if k = 0 then Pi.single i (1 : ℝ) else Pi.single j (1 : ℝ)
  rw [quadForm_iteratedFDeriv_two]
  simp [m, Finset.sum_add_distrib]
  have h1 : (∑ a : Fin 4, ∑ b : Fin 4,
      ((Pi.single i (1 : ℝ) : E) a) * Sig a b * ((Pi.single j (1 : ℝ) : E) b)) = Sig i j := by
    rw [Fintype.sum_eq_single i (by
      intro a ha
      simp [Pi.single_eq_of_ne ha])]
    rw [Fintype.sum_eq_single j (by
      intro b hb
      simp [Pi.single_eq_of_ne hb])]
    simp [Pi.single_eq_same]
  have h2 : (∑ a : Fin 4, ∑ b : Fin 4,
      ((Pi.single j (1 : ℝ) : E) a) * Sig a b * ((Pi.single i (1 : ℝ) : E) b)) = Sig j i := by
    rw [Fintype.sum_eq_single j (by
      intro a ha
      simp [Pi.single_eq_of_ne ha])]
    rw [Fintype.sum_eq_single i (by
      intro b hb
      simp [Pi.single_eq_of_ne hb])]
    simp [Pi.single_eq_same]
  rw [h1, h2]
  rw [Matrix.IsSymm.apply hSymm i j]
  ring

/-- The third iterated derivative of a quadratic form vanishes identically. -/
lemma iteratedFDeriv_quadForm_three (Sig : Matrix (Fin 4) (Fin 4) ℝ) (x : E) :
    iteratedFDeriv ℝ 3 (fun t : E => quadForm Sig t) x = 0 := by
  ext m
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
    (f := fun t : E => quadForm Sig t) (differentiableAt_iteratedFDeriv_quadForm Sig 2 x)]
  have hconst : (fun y : E => iteratedFDeriv ℝ 2 (fun t : E => quadForm Sig t) y (Fin.tail m)) =
      (fun _ : E => (1/2) * (∑ a : Fin 4, ∑ b : Fin 4,
        ((Fin.tail m) 0 a * Sig a b * (Fin.tail m) 1 b +
         (Fin.tail m) 1 a * Sig a b * (Fin.tail m) 0 b))) := by
    funext y
    exact quadForm_iteratedFDeriv_two Sig y (Fin.tail m)
  rw [hconst]
  simp

/-- `quadForm` is degree-2: all Fréchet derivatives of order ≥ 3 vanish identically. -/
lemma iteratedFDeriv_quadForm_ge_three (Sig : Matrix (Fin 4) (Fin 4) ℝ) (n : ℕ)
    (hn : 3 ≤ n) :
    ∀ x : E, iteratedFDeriv ℝ n (fun t : E => quadForm Sig t) x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 + k := ⟨n - 3, by omega⟩
  induction k with
  | zero =>
      intro x
      simpa using iteratedFDeriv_quadForm_three Sig x
  | succ k ih =>
      intro x
      have hs : 3 + (k + 1) = (3 + k) + 1 := by omega
      rw [hs]
      have hrew : iteratedFDeriv ℝ (3 + k) (fun t : E => quadForm Sig t) =
          (fun _ : E => 0) := by
        funext y
        exact (ih (by omega)) y
      ext m
      rw [iteratedFDeriv_succ_apply_left]
      rw [hrew]
      simp

/-- `quadForm` is degree-2: all Fréchet derivatives of order ≥ 3 vanish identically. -/
lemma quadForm_high_deriv_zero
    (Sig : Matrix (Fin 4) (Fin 4) ℝ) (n : ℕ) (hn : 3 ≤ n) :
    iteratedFDeriv ℝ n (fun t : E => quadForm Sig t) 0 = 0 := by
  exact iteratedFDeriv_quadForm_ge_three Sig n hn 0

/-! ### The `mgf = exp ∘ quadForm` derivative chain -/

/-- The constant symmetric bilinear form `D²(quadForm)`: `(a,b) ↦ ½·Σᵢⱼ(aᵢ·Sigᵢⱼ·bⱼ+bᵢ·Sigᵢⱼ·aⱼ)`. -/
def qd2 (Sig : Matrix (Fin 4) (Fin 4) ℝ) (a b : E) : ℝ :=
  (1 / 2 : ℝ) * (∑ i : Fin 4, ∑ j : Fin 4, (a i * Sig i j * b j + b i * Sig i j * a j))

/-- `quadForm` vanishes at `0`. -/
lemma quadForm_zero (Sig : Matrix (Fin 4) (Fin 4) ℝ) : quadForm Sig 0 = 0 := by
  simp [quadForm]

/-- The first `fderiv` of the quadratic form vanishes at `0`. -/
@[simp]
lemma quadForm_fderiv_zero (Sig : Matrix (Fin 4) (Fin 4) ℝ) :
    fderiv ℝ (fun t : E => quadForm Sig t) 0 = 0 := by
  ext w
  rw [quadForm_fderiv_apply]
  simp

/-- The exponential `mgf = exp ∘ quadForm` is smooth. -/
lemma contDiff_mgf (Sig : Matrix (Fin 4) (Fin 4) ℝ) : ContDiff ℝ ⊤ (mgf Sig) := by
  unfold mgf
  simpa [Function.comp_def] using (Real.contDiff_exp.comp (contDiff_quadForm Sig))

/-- Any fixed-order `iteratedFDeriv` of the smooth function `mgf` is differentiable. -/
lemma differentiableAt_iteratedFDeriv_mgf (Sig : Matrix (Fin 4) (Fin 4) ℝ) (m : ℕ) (x : E) :
    DifferentiableAt ℝ (fun y : E => iteratedFDeriv ℝ m (mgf Sig) y) x := by
  exact (contDiff_mgf Sig).contDiffAt.differentiableAt_iteratedFDeriv (m := m) (by simp)

/-- Chain rule: `fderiv (mgf Sig) x v = exp(Qx) · fderiv (quadForm Sig) x v`. -/
lemma mgf_fderiv_apply (Sig : Matrix (Fin 4) (Fin 4) ℝ) (x v : E) :
    fderiv ℝ (mgf Sig) x v =
      Real.exp (quadForm Sig x) * fderiv ℝ (fun t : E => quadForm Sig t) x v := by
  have hfderiv : HasFDerivAt (fun t : E => quadForm Sig t)
      (fderiv ℝ (fun t : E => quadForm Sig t) x) x :=
    (contDiff_quadForm Sig).contDiffAt.differentiableAt (by simp) |>.hasFDerivAt
  have h := hfderiv.exp
  change fderiv ℝ (fun y : E => Real.exp (quadForm Sig y)) x v = _
  rw [h.fderiv]
  simp

/-- The `fderiv` of `x ↦ fderiv(quadForm) x w` is `a ↦ qd2(a,w)`. -/
@[simp]
lemma quadForm_fderiv_fderiv_apply (Sig : Matrix (Fin 4) (Fin 4) ℝ) (x w v : E) :
    fderiv ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y w) x v = qd2 Sig v w := by
  have hfun : (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y w) =
      (fun y : E => (1/2) * (∑ i : Fin 4, ∑ j : Fin 4, (y i * Sig i j * w j + w i * Sig i j * y j))) := by
    funext y
    exact quadForm_fderiv_apply Sig y w
  rw [hfun]
  have hD : DifferentiableAt ℝ
      (fun y : E => ∑ i : Fin 4, ∑ j : Fin 4, (y i * Sig i j * w j + w i * Sig i j * y j)) x := by
    fun_prop
  rw [fderiv_const_mul hD]
  simp only [smul_apply, smul_eq_mul]
  have hdsum := fderiv_double_sum_apply x
    (F := fun a b : Fin 4 => (fun y : E => y a * Sig a b * w b + w a * Sig a b * y b))
    (by intro a b; fun_prop)
  rw [hdsum]
  simp only [clm_sum_apply]
  simp [qd2]

/-- `x ↦ fderiv(quadForm) x` is smooth as a function into continuous linear maps. -/
lemma fderiv_quadForm_clm (Sig : Matrix (Fin 4) (Fin 4) ℝ) :
    ContDiff ℝ ⊤ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y) :=
  (contDiff_quadForm Sig).fderiv_right (by simp)

/-- For a fixed direction, `x ↦ fderiv(quadForm) x w` is differentiable. -/
lemma differentiableAt_fderiv_quadForm_apply (Sig : Matrix (Fin 4) (Fin 4) ℝ) (w : E) (x : E) :
    DifferentiableAt ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y w) x := by
  have hc : ContDiff ℝ ⊤ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y w) :=
    (fderiv_quadForm_clm Sig).clm_apply (contDiff_const : ContDiff ℝ ⊤ (fun _ : E => w))
  exact hc.contDiffAt.differentiableAt (by simp)

/-- The `mgf` derivative at `0` along `x ↦ exp(Qx)·G(x)`: `DQ(0) = 0` kills the first factor,
    leaving exactly `fderiv G 0 a`. -/
lemma fderiv_exp_mul_at_zero (Sig : Matrix (Fin 4) (Fin 4) ℝ) (a : E) (G : E → ℝ)
    (hG : DifferentiableAt ℝ G 0) {G' : ℝ}
    (hGa : fderiv ℝ G 0 a = G') :
    fderiv ℝ (fun x : E => Real.exp (quadForm Sig x) * G x) 0 a = G' := by
  have hc : DifferentiableAt ℝ (fun y : E => Real.exp (quadForm Sig y)) 0 :=
    (contDiff_mgf Sig).contDiffAt.differentiableAt (by simp)
  rw [fderiv_fun_mul hc hG]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hfirst : fderiv ℝ (fun y : E => Real.exp (quadForm Sig y)) 0 a = 0 := by
    have h := mgf_fderiv_apply Sig 0 a
    have hq0 : quadForm Sig 0 = 0 := by simp [quadForm]
    have hfq : fderiv ℝ (fun t : E => quadForm Sig t) 0 a = 0 := by
      rw [quadForm_fderiv_zero]
      rfl
    change fderiv ℝ (mgf Sig) 0 a = 0
    rw [h, hq0, hfq]
    norm_num
  rw [hfirst]
  have hq0 : quadForm Sig 0 = 0 := by simp [quadForm]
  simp [hq0, hGa]

/-- Second-order: `D²(mgf) x (a,b) = exp(Qx)·(DQ(x)(a)·DQ(x)(b) + QD2(a,b))`. -/
lemma mgf_D2 (Sig : Matrix (Fin 4) (Fin 4) ℝ) (x : E) (m : Fin 2 → E) :
    (iteratedFDeriv ℝ 2 (mgf Sig) x) m =
      Real.exp (quadForm Sig x) *
        (fderiv ℝ (fun t : E => quadForm Sig t) x (m 0) *
           fderiv ℝ (fun t : E => quadForm Sig t) x (m 1) +
         qd2 Sig (m 0) (m 1)) := by
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
    (f := mgf Sig) (differentiableAt_iteratedFDeriv_mgf Sig 1 x)]
  simp only [iteratedFDeriv_one_apply]
  have htail : (Fin.tail m) 0 = m 1 := rfl
  rw [htail]
  have hfun : (fun y : E => fderiv ℝ (mgf Sig) y (m 1)) =
      (fun y : E => Real.exp (quadForm Sig y) * fderiv ℝ (fun t : E => quadForm Sig t) y (m 1)) := by
    funext y
    exact mgf_fderiv_apply Sig y (m 1)
  rw [hfun]
  have hc : DifferentiableAt ℝ (fun y : E => Real.exp (quadForm Sig y)) x :=
    (contDiff_mgf Sig).contDiffAt.differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1)) x :=
    differentiableAt_fderiv_quadForm_apply Sig (m 1) x
  rw [fderiv_fun_mul hc hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hfp : fderiv ℝ (fun y : E => Real.exp (quadForm Sig y)) x (m 0) =
      Real.exp (quadForm Sig x) * fderiv ℝ (fun t : E => quadForm Sig t) x (m 0) := by
    change fderiv ℝ (mgf Sig) x (m 0) = _
    exact mgf_fderiv_apply Sig x (m 0)
  have hfq : fderiv ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1)) x (m 0) =
      qd2 Sig (m 0) (m 1) := quadForm_fderiv_fderiv_apply Sig x (m 1) (m 0)
  rw [hfp, hfq]
  ring

/-- Third-order: `D³(mgf) x (a,b,c)` — the three `Q DQ` terms survive. -/
lemma mgf_D3 (Sig : Matrix (Fin 4) (Fin 4) ℝ) (x : E) (m : Fin 3 → E) :
    (iteratedFDeriv ℝ 3 (mgf Sig) x) m =
      Real.exp (quadForm Sig x) *
        (fderiv ℝ (fun t : E => quadForm Sig t) x (m 0) *
           fderiv ℝ (fun t : E => quadForm Sig t) x (m 1) *
           fderiv ℝ (fun t : E => quadForm Sig t) x (m 2) +
         fderiv ℝ (fun t : E => quadForm Sig t) x (m 0) * qd2 Sig (m 1) (m 2) +
         fderiv ℝ (fun t : E => quadForm Sig t) x (m 1) * qd2 Sig (m 0) (m 2) +
         fderiv ℝ (fun t : E => quadForm Sig t) x (m 2) * qd2 Sig (m 0) (m 1)) := by
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
    (f := mgf Sig) (differentiableAt_iteratedFDeriv_mgf Sig 2 x)]
  have hfun : (fun y : E => iteratedFDeriv ℝ 2 (mgf Sig) y (Fin.tail m)) =
      (fun y : E => Real.exp (quadForm Sig y) *
        (fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) *
           fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) +
         qd2 Sig (m 1) (m 2))) := by
    funext y
    rw [mgf_D2 Sig y (Fin.tail m)]
    simp [Fin.tail]
  rw [hfun]
  have hc : DifferentiableAt ℝ (fun y : E => Real.exp (quadForm Sig y)) x :=
    (contDiff_mgf Sig).contDiffAt.differentiableAt (by simp)
  have hA : DifferentiableAt ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1)) x :=
    differentiableAt_fderiv_quadForm_apply Sig (m 1) x
  have hB : DifferentiableAt ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 2)) x :=
    differentiableAt_fderiv_quadForm_apply Sig (m 2) x
  rw [fderiv_fun_mul hc (by fun_prop)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hfp : fderiv ℝ (fun y : E => Real.exp (quadForm Sig y)) x (m 0) =
      Real.exp (quadForm Sig x) * fderiv ℝ (fun t : E => quadForm Sig t) x (m 0) := by
    change fderiv ℝ (mgf Sig) x (m 0) = _
    exact mgf_fderiv_apply Sig x (m 0)
  rw [hfp]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_fun_mul hA hB]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hfA : fderiv ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1)) x (m 0) =
      qd2 Sig (m 0) (m 1) := quadForm_fderiv_fderiv_apply Sig x (m 1) (m 0)
  have hfB : fderiv ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 2)) x (m 0) =
      qd2 Sig (m 0) (m 2) := quadForm_fderiv_fderiv_apply Sig x (m 2) (m 0)
  rw [hfA, hfB]
  simp
  ring

/-- The `fderiv` of a four-term sum splits into the sum of the four `fderiv`s. -/
lemma fderiv_sum4 (x : E) (v : E) (A B C D : E → ℝ)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hC : DifferentiableAt ℝ C x) (hD : DifferentiableAt ℝ D x) :
    fderiv ℝ (fun y : E => A y + B y + C y + D y) x v =
      fderiv ℝ A x v + fderiv ℝ B x v + fderiv ℝ C x v + fderiv ℝ D x v := by
  rw [fderiv_fun_add (by fun_prop) hD]
  rw [fderiv_fun_add (by fun_prop) hC]
  rw [fderiv_fun_add hA hB]
  simp only [ContinuousLinearMap.add_apply]

/-- Fourth-order at `0`: only the three `2+2` pairings survive the `DQ(0) = 0` pruning. -/
lemma mgf_D4_at_zero (Sig : Matrix (Fin 4) (Fin 4) ℝ) (m : Fin 4 → E) :
    (iteratedFDeriv ℝ 4 (mgf Sig) 0) m =
      qd2 Sig (m 0) (m 1) * qd2 Sig (m 2) (m 3) +
      qd2 Sig (m 0) (m 2) * qd2 Sig (m 1) (m 3) +
      qd2 Sig (m 0) (m 3) * qd2 Sig (m 1) (m 2) := by
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
    (f := mgf Sig) (differentiableAt_iteratedFDeriv_mgf Sig 3 0)]
  have hfun : (fun y : E => iteratedFDeriv ℝ 3 (mgf Sig) y (Fin.tail m)) =
      (fun y : E => Real.exp (quadForm Sig y) *
        (fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) *
           fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) *
           fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) +
         fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) * qd2 Sig (m 2) (m 3) +
         fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) * qd2 Sig (m 1) (m 3) +
         fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) * qd2 Sig (m 1) (m 2))) := by
    funext y
    rw [mgf_D3 Sig y (Fin.tail m)]
    simp [Fin.tail]
  rw [hfun]
  have hA : DifferentiableAt ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1)) 0 :=
    differentiableAt_fderiv_quadForm_apply Sig (m 1) 0
  have hB : DifferentiableAt ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 2)) 0 :=
    differentiableAt_fderiv_quadForm_apply Sig (m 2) 0
  have hC : DifferentiableAt ℝ (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 3)) 0 :=
    differentiableAt_fderiv_quadForm_apply Sig (m 3) 0
  have hG : DifferentiableAt ℝ (fun y : E =>
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) *
        fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) *
        fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) * qd2 Sig (m 2) (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) * qd2 Sig (m 1) (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) * qd2 Sig (m 1) (m 2)) 0 := by
    fun_prop
  have hF1 : fderiv ℝ
      (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) *
        fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) *
        fderiv ℝ (fun t : E => quadForm Sig t) y (m 3)) 0 (m 0) = 0 := by
    rw [fderiv_fun_mul (by fun_prop) hC]
    simp [quadForm_fderiv_zero]
  have hF2 : fderiv ℝ
      (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) * qd2 Sig (m 2) (m 3)) 0 (m 0) =
      qd2 Sig (m 0) (m 1) * qd2 Sig (m 2) (m 3) := by
    rw [fderiv_fun_mul hA (by fun_prop)]
    simp
    ring
  have hF3 : fderiv ℝ
      (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) * qd2 Sig (m 1) (m 3)) 0 (m 0) =
      qd2 Sig (m 0) (m 2) * qd2 Sig (m 1) (m 3) := by
    rw [fderiv_fun_mul hB (by fun_prop)]
    simp
    ring
  have hF4 : fderiv ℝ
      (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) * qd2 Sig (m 1) (m 2)) 0 (m 0) =
      qd2 Sig (m 0) (m 3) * qd2 Sig (m 1) (m 2) := by
    rw [fderiv_fun_mul hC (by fun_prop)]
    simp
    ring
  have hsum := fderiv_sum4 0 (m 0)
    (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) *
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) *
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 3))
    (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) * qd2 Sig (m 2) (m 3))
    (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) * qd2 Sig (m 1) (m 3))
    (fun y : E => fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) * qd2 Sig (m 1) (m 2))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hGa : fderiv ℝ (fun y : E =>
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) *
        fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) *
        fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) * qd2 Sig (m 2) (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) * qd2 Sig (m 1) (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) * qd2 Sig (m 1) (m 2)) 0 (m 0) =
      qd2 Sig (m 0) (m 1) * qd2 Sig (m 2) (m 3) +
      qd2 Sig (m 0) (m 2) * qd2 Sig (m 1) (m 3) +
      qd2 Sig (m 0) (m 3) * qd2 Sig (m 1) (m 2) := by
    rw [hsum]
    rw [hF1, hF2, hF3, hF4]
    ring
  exact fderiv_exp_mul_at_zero Sig (m 0)
    (fun y : E =>
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) *
        fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) *
        fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 1) * qd2 Sig (m 2) (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 2) * qd2 Sig (m 1) (m 3) +
      fderiv ℝ (fun t : E => quadForm Sig t) y (m 3) * qd2 Sig (m 1) (m 2)) hG hGa

/-- `QD2(singleᵢ1, singleⱼ1) = Sigᵢⱼ` by the second partial of the quadratic form. -/
lemma qd2_single (Sig : Matrix (Fin 4) (Fin 4) ℝ) (hSymm : Sig.IsSymm) (i j : Fin 4) :
    qd2 Sig (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) = Sig i j := by
  have h := quadForm_second_partial Sig hSymm i j
  rw [quadForm_iteratedFDeriv_two Sig 0
    (fun k : Fin 2 => if k = 0 then Pi.single i (1 : ℝ) else Pi.single j (1 : ℝ))] at h
  unfold qd2
  simpa using h

/-- Chain-rule step for `Real.exp ∘ quadForm`: the 4-th mixed derivative at 0
    equals the Isserlis pair-sum.  Proof plan (verified algebra core of the whole
    project, cf. `verify/schwinger.py::check_isserlis_4pt`):
      ① Faa di Bruno / Bell for n=4: only the 2+2 set partitions of {0,1,2,3}
         survive (all `quadForm` derivatives of order ≥ 3 vanish, `exp` coefs = 1);
      ② each 2+2 partition {i,j},{k,l} contributes `(∂ᵢ∂ⱼ quadForm|₀)·(∂ₖ∂ₗ quadForm|₀)
         = Sigᵢⱼ·Sigₖₗ` by `quadForm_second_partial` + `hSymm`;
      ③ the three surviving partitions are (0,1)(2,3), (0,2)(1,3), (0,3)(1,2)
         ⇒ `Sig₀₁Sig₂₃ + Sig₀₂Sig₁₃ + Sig₀₃Sig₁₂` = `isserlisRHS Sig`. -/
lemma mgf_deriv_exp_chain (Sig : Matrix (Fin 4) (Fin 4) ℝ) (hSymm : Sig.IsSymm) :
    (iteratedFDeriv ℝ 4 (mgf Sig) 0) (fun i : Fin 4 => Pi.single i 1) = isserlisRHS Sig := by
  have h := mgf_D4_at_zero Sig (fun i : Fin 4 => Pi.single i 1)
  rw [h]
  have h01 : qd2 Sig (Pi.single 0 (1 : ℝ)) (Pi.single 1 (1 : ℝ)) = Sig 0 1 := qd2_single Sig hSymm 0 1
  have h02 : qd2 Sig (Pi.single 0 (1 : ℝ)) (Pi.single 2 (1 : ℝ)) = Sig 0 2 := qd2_single Sig hSymm 0 2
  have h03 : qd2 Sig (Pi.single 0 (1 : ℝ)) (Pi.single 3 (1 : ℝ)) = Sig 0 3 := qd2_single Sig hSymm 0 3
  have h12 : qd2 Sig (Pi.single 1 (1 : ℝ)) (Pi.single 2 (1 : ℝ)) = Sig 1 2 := qd2_single Sig hSymm 1 2
  have h13 : qd2 Sig (Pi.single 1 (1 : ℝ)) (Pi.single 3 (1 : ℝ)) = Sig 1 3 := qd2_single Sig hSymm 1 3
  have h23 : qd2 Sig (Pi.single 2 (1 : ℝ)) (Pi.single 3 (1 : ℝ)) = Sig 2 3 := qd2_single Sig hSymm 2 3
  simp [h01, h02, h03, h12, h13, h23, isserlisRHS]

/-- **Isserlis, n=4** (lemma [L15]; GR/Janson; the algebra core of S7).  For a
symmetric covariance `Sig`, the fourth mgf-derivative equals the matching sum. -/
theorem isserlis_4pt (Sig : Matrix (Fin 4) (Fin 4) ℝ) (hSymm : Sig.IsSymm) :
    fourthMoment Sig = isserlisRHS Sig := by
  -- `fourthMoment` is definitionally the mgf 4-th mixed derivative.
  exact mgf_deriv_exp_chain Sig hSymm

end S6