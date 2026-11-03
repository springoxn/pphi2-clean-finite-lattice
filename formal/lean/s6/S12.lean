import S6Isserlis.S11

/-!
# S12 — finite-dimensional Gauss–Wick, all `n` (P3b-i (iii))

`E[∏ᵢ Xᵢ] = Σ_{M ∈ matchings n} ∏_{e ∈ M} Σ_{ij}` for a centred Gaussian vector.

The Gaussian is encoded exactly as in `S6.lean`: by its moment generating function
`t ↦ exp (½ tᵀΣt)`, and the mixed moment of order `n` is the `n`-th iterated Fréchet
derivative of the mgf at `0`.  The right-hand side is the symmetric multilinear pairing form
`pairingML (bSig Σ)` of `S11.lean`.

Route (the one recorded in the frontier card):

* `iteratedDeriv_exp_sq` — the **one-dimensional Gaussian moment**
  `dⁿ/dtⁿ exp(c t²)|₀ = (2c)^{n/2} · #(matchings n)`, proved from the ODE `H' = 2ct·H`
  by two-step induction, together with the matching count `#(matchings (n+2)) = (n+1)·#(matchings n)`
  and `matchings n = ∅` for odd `n` (a perfect matching of `Fin n` has `n/2` pairs, `S11.lean`);
* `iteratedFDeriv_apply_diagonal` — the iterated derivative on the diagonal `(g,…,g)` is the
  iterated derivative of the restriction to the line `t ↦ x + t • g`;
* `pairingML_isSymm` (`S11.lean`) and `ContDiffAt.iteratedFDeriv_comp_perm` (Mathlib) give the
  symmetry of both sides;
* `eq_of_diagonal_eq` (`S7.lean`, the polarisation/diagonal-determinacy lemma) upgrades the
  equality of diagonal values to the equality of multilinear forms.

This is the finite-dimensional algebraic core of `wick.tex`; the measure-theoretic step
(`∫ ∏ φ(f_j) dμ_m = Ψ`, i.e. P3b-ii) is separate.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped BigOperators
open Classical

namespace Schwinger

/-! ### The one-dimensional Gaussian moment -/

/-- `iteratedDeriv i (t ↦ a · t) 0`. -/
lemma iteratedDeriv_mul_self (a : ℝ) (i : ℕ) :
    iteratedDeriv i (fun t : ℝ => a * t) 0 = if i = 1 then a else 0 := by
  have h : (fun t : ℝ => a * t) = a • (id : ℝ → ℝ) := rfl
  rw [h, iteratedDeriv_const_smul (contDiffAt_id (n := (i : WithTop ℕ∞)))]
  rw [iteratedDeriv_id]
  by_cases h1 : i = 1
  · subst h1; simp
  · by_cases h0 : i = 0 <;> simp [h0, h1]

/-- The derivative of `t ↦ exp (c t²)`, as a function. -/
lemma deriv_exp_sq (c : ℝ) :
    deriv (fun t : ℝ => Real.exp (c * t ^ 2)) = fun t => (2 * c * t) * Real.exp (c * t ^ 2) := by
  funext t
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have h1 : HasDerivAt (fun s : ℝ => c * s ^ 2) (c * (2 * t)) t := h2.const_mul c
  rw [h1.exp.deriv]
  ring

/-- The recursion for the moments of `exp (c t²)`: `a_{m+2} = 2c (m+1) a_m`. -/
lemma iteratedDeriv_exp_sq_add_two (c : ℝ) (m : ℕ) :
    iteratedDeriv (m + 2) (fun t : ℝ => Real.exp (c * t ^ 2)) 0
      = 2 * c * (m + 1) * iteratedDeriv m (fun t : ℝ => Real.exp (c * t ^ 2)) 0 := by
  rw [iteratedDeriv_succ', deriv_exp_sq]
  rw [iteratedDeriv_fun_mul (n := m + 1) (f := fun t : ℝ => 2 * c * t)
    (g := fun t : ℝ => Real.exp (c * t ^ 2)) (x := 0) (by fun_prop) (by fun_prop)]
  rw [Finset.sum_eq_single 1]
  · have h2c : iteratedDeriv 1 (fun t : ℝ => 2 * c * t) 0 = 2 * c := by
      rw [iteratedDeriv_mul_self]
      norm_num
    rw [Nat.choose_one_right, h2c, show m + 1 - 1 = m from by omega]
    push_cast
    ring
  · intro b _ hb
    have hb0 : iteratedDeriv b (fun t : ℝ => 2 * c * t) 0 = 0 := by
      rw [iteratedDeriv_mul_self]
      simp [hb]
    rw [hb0]
    ring
  · intro h1
    exact absurd (Finset.mem_range.mpr (by omega)) h1

/-! ### `matchings n` is empty for odd `n` -/

/-- Every perfect matching of `Fin n` has an even number of vertices. -/
lemma even_of_mem_matchings {M : Finset (Sym2 (Fin n))} (hM : M ∈ matchings n) : Even n :=
  ⟨M.card, by have h := card_mul_two_of_isPerfectMatching (mem_matchings.mp hM); omega⟩

/-- There is no perfect matching of `Fin n` for odd `n`. -/
lemma card_matchings_of_odd {n : ℕ} (hn : ¬ Even n) : (matchings n).card = 0 := by
  by_contra h
  obtain ⟨M, hM⟩ := Finset.card_pos.mp (Nat.pos_iff_ne_zero.mpr h)
  exact hn (even_of_mem_matchings hM)

/-- The matching recursion, including the case `n = 0`. -/
lemma card_matchings_add_two' (n : ℕ) :
    (matchings (n + 2)).card = (n + 1) * (matchings n).card := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp [card_matchings_two, card_matchings_zero]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact card_matchings_add_two

/-- **The one-dimensional Gaussian moment.** -/
lemma iteratedDeriv_exp_sq (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Real.exp (c * t ^ 2)) 0
      = (2 * c) ^ (n / 2) * (matchings n).card := by
  induction n using Nat.twoStepInduction with
  | zero => rw [iteratedDeriv_zero, card_matchings_zero]; simp
  | one =>
    have h1 : (matchings 1).card = 0 :=
      card_matchings_of_odd (n := 1) (by rintro ⟨r, hr⟩; omega)
    rw [iteratedDeriv_one, deriv_exp_sq, h1]
    simp
  | more n ih _ =>
    rw [iteratedDeriv_exp_sq_add_two c n, ih, card_matchings_add_two' n]
    rw [show (n + 2) / 2 = n / 2 + 1 from by omega, pow_succ]
    push_cast
    ring

/-! ### The finite-dimensional Gaussian -/

variable {d : ℕ}

/-- The quadratic form `½ tᵀΣt`. -/
def quadFormD (Sig : Matrix (Fin d) (Fin d) ℝ) (t : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, t i * Sig i j * t j

/-- The moment generating function of the centred Gaussian with covariance `Σ`. -/
def mgfD (Sig : Matrix (Fin d) (Fin d) ℝ) (t : Fin d → ℝ) : ℝ :=
  Real.exp (quadFormD Sig t)

/-- The covariance bilinear form `B u v = uᵀΣv`. -/
def bSig (Sig : Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∑ i, ∑ j, u i * Sig i j * v j)
    (fun u₁ u₂ v => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring)
    (fun u v₁ v₂ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring)

/-- The defining formula of the covariance form. -/
lemma bSig_apply (Sig : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) :
    bSig Sig u v = ∑ i, ∑ j, u i * Sig i j * v j := by
  simp only [bSig, LinearMap.mk₂_apply]

/-- The covariance form is symmetric. -/
lemma bSig_isSymm (Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig.IsSymm) :
    ∀ u v : Fin d → ℝ, bSig Sig u v = bSig Sig v u := by
  intro u v
  rw [bSig_apply, bSig_apply]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [Matrix.IsSymm.apply hSig j i]; ring

/-- The diagonal of the covariance form is twice the quadratic form. -/
lemma bSig_self (Sig : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    bSig Sig v v = 2 * quadFormD Sig v := by
  rw [bSig_apply]
  unfold quadFormD
  ring

/-- `quadFormD` is homogeneous of degree two. -/
lemma quadFormD_smul (Sig : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (g : Fin d → ℝ) :
    quadFormD Sig (t • g) = t ^ 2 * quadFormD Sig g := by
  have h : ∀ i j : Fin d, (t • g) i * Sig i j * (t • g) j = t ^ 2 * (g i * Sig i j * g j) := by
    intro i j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  unfold quadFormD
  simp only [h, ← Finset.mul_sum]
  ring

/-- `quadFormD` is analytic. -/
lemma analyticAt_quadFormD (Sig : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    AnalyticAt ℝ (quadFormD Sig) x := by
  unfold quadFormD
  refine AnalyticAt.mul analyticAt_const ?_
  refine Finset.analyticAt_fun_sum Finset.univ fun i _ => ?_
  refine Finset.analyticAt_fun_sum Finset.univ fun j _ => ?_
  exact ((ContinuousLinearMap.analyticAt
      (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) x).mul analyticAt_const).mul
    (ContinuousLinearMap.analyticAt (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ) x)

/-- The mgf is analytic. -/
lemma analyticAt_mgfD (Sig : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    AnalyticAt ℝ (mgfD Sig) x :=
  (analyticAt_rexp (x := quadFormD Sig x)).comp (analyticAt_quadFormD Sig x)

/-- The mgf is smooth, at every finite order. -/
lemma contDiff_mgfD (Sig : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) (mgfD Sig) := by
  unfold mgfD quadFormD
  fun_prop

/-! ### The iterated derivative on the diagonal -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `n`-th iterated derivative at `x`, evaluated on the `n`-tuple `(g, …, g)`, is the `n`-th
derivative at `0` of the restriction to the line `t ↦ x + t • g`. -/
lemma iteratedFDeriv_apply_diagonal (f : E → ℝ) (x g : E) (n : ℕ)
    (hf : ContDiff ℝ (n : WithTop ℕ∞) (fun z : E => f (x + z))) :
    (iteratedFDeriv ℝ n f x) (fun _ : Fin n => g)
      = iteratedDeriv n (fun t : ℝ => f (x + t • g)) 0 := by
  have hL : ∀ t : ℝ, (ContinuousLinearMap.toSpanSingleton ℝ g) t = t • g :=
    fun t => ContinuousLinearMap.toSpanSingleton_apply ℝ g t
  have hfun : (fun t : ℝ => f (x + t • g))
      = (fun z : E => f (x + z)) ∘ (ContinuousLinearMap.toSpanSingleton ℝ g) := by
    funext t
    rw [Function.comp_apply, hL]
  have hstep : (iteratedFDeriv ℝ n (fun t : ℝ => f (x + t • g)) 0)
      = (iteratedFDeriv ℝ n f x).compContinuousLinearMap (fun _ : Fin n => ContinuousLinearMap.toSpanSingleton ℝ g) := by
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right
      (ContinuousLinearMap.toSpanSingleton ℝ g) hf 0 le_rfl]
    rw [show (ContinuousLinearMap.toSpanSingleton ℝ g) 0 = (0 : E) from by
      rw [hL, zero_smul]]
    rw [iteratedFDeriv_comp_add_left, add_zero]
  rw [iteratedDeriv_eq_iteratedFDeriv, hstep, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-! ### Gauss–Wick -/

/-- **Finite-dimensional Gauss–Wick, all `n`** (P3b-i (iii); `S6.isserlis_4pt` is the case `n = 4`).
For a centred Gaussian vector with symmetric covariance `Σ`, the `n`-th mixed moment of the
linear statistics `v i` is the sum over all perfect matchings of the products of pair
covariances `B(v i, v j) = (v i)ᵀ Σ (v j)`. -/
theorem gauss_wick (Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig.IsSymm) (n : ℕ)
    (v : Fin n → (Fin d → ℝ)) :
    (iteratedFDeriv ℝ n (mgfD Sig) 0) v
      = pairingML (bSig Sig) (bSig_isSymm Sig hSig) n v := by
  have hc : ContDiffAt ℝ ⊤ (mgfD Sig) 0 := (analyticAt_mgfD Sig 0).contDiffAt
  have hshift : ContDiff ℝ (↑n) (fun z : Fin d → ℝ => mgfD Sig (0 + z)) := by
    have h1 : ContDiff ℝ (↑n) (mgfD Sig) := contDiff_mgfD Sig n
    have h2 : ContDiff ℝ (↑n) (fun z : Fin d → ℝ => (0 : Fin d → ℝ) + z) := by fun_prop
    exact h1.comp h2
  have hΦ : IsSymmMultilinear ((iteratedFDeriv ℝ n (mgfD Sig) 0).toMultilinearMap) :=
    fun σ v => ContDiffAt.iteratedFDeriv_comp_perm hc v σ
  have hΨ : IsSymmMultilinear (pairingML (bSig Sig) (bSig_isSymm Sig hSig) n) :=
    pairingML_isSymm (bSig Sig) (bSig_isSymm Sig hSig) n
  have hdiag : ∀ g : Fin d → ℝ,
      (iteratedFDeriv ℝ n (mgfD Sig) 0).toMultilinearMap (fun _ : Fin n => g)
        = pairingML (bSig Sig) (bSig_isSymm Sig hSig) n (fun _ : Fin n => g) := fun g => by
    have hsplit : (fun t : ℝ => mgfD Sig (0 + t • g))
        = (fun t : ℝ => Real.exp (quadFormD Sig g * t ^ 2)) := by
      funext t
      rw [zero_add, mgfD, quadFormD_smul, mul_comm]
    show (iteratedFDeriv ℝ n (mgfD Sig) 0) (fun _ : Fin n => g) = _
    rw [iteratedFDeriv_apply_diagonal (mgfD Sig) 0 g n hshift, hsplit, iteratedDeriv_exp_sq,
      pairingML_const, bSig_self]
  have h := eq_of_diagonal_eq ((iteratedFDeriv ℝ n (mgfD Sig) 0).toMultilinearMap)
    (pairingML (bSig Sig) (bSig_isSymm Sig hSig) n) hΦ hΨ hdiag
  rw [← h]
  simp only [ContinuousMultilinearMap.coe_coe]

end Schwinger
