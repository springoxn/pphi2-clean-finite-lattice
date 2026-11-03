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

/-- The quadratic form `t ↦ ½ · tᵀSigt`, expanded as `½ · ∑ᵢⱼ tᵢ·Sigᵢⱼ·tⱼ`. -/
def quadForm (Sig : Matrix (Fin 4) (Fin 4) ℝ) (t : Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i : Fin 4, ∑ j : Fin 4, t i * Sig i j * t j)

/-- mgf of a 0-mean Gaussian with covariance `Sig`: `M(t) = exp(quadForm Sig t)`. -/
def mgf (Sig : Matrix (Fin 4) (Fin 4) ℝ) (t : Fin 4 → ℝ) : ℝ :=
  Real.exp (quadForm Sig t)

/-- Fourth mixed moment, mgf-definition:
    `E[X₁X₂X₃X₄] := M⁗(0)(e₁,e₂,e₃,e₄)` where `eᵢ = Pi.single i 1`. -/
def fourthMoment (Sig : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (iteratedFDeriv ℝ 4 (mgf Sig) 0) (fun i : Fin 4 => Pi.single i 1)

/-- The right-hand side of Isserlis: sum over the three perfect matchings. -/
def isserlisRHS (Sig : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Sig 0 1 * Sig 2 3 + Sig 0 2 * Sig 1 3 + Sig 0 3 * Sig 1 2

/-! ### Helper lemmas (statements pinned; proofs `sorry` until the compile loop) -/

/-- `quadForm` is quadratic: the mixed second partial in directions `eᵢ,eⱼ` at `0`
    equals the matrix entry `Sigᵢⱼ` (symmetry is what removes the ½). -/
lemma quadForm_second_partial
    (Sig : Matrix (Fin 4) (Fin 4) ℝ) (hSymm : Sig.IsSymm) (i j : Fin 4) :
    (iteratedFDeriv ℝ 2 (fun t : Fin 4 → ℝ => quadForm Sig t) 0)
        (fun k : Fin 2 => if k = 0 then Pi.single i 1 else Pi.single j 1)
          = Sig i j := by
  -- ① expand quadForm = ½ · ∑_{p,q} tₚ Sigₚq t_q  (Matrix.dotProduct_def / mulVec);
  -- ② second Fréchet derivative of a quadratic is the constant bilinear form
  --    (u,v) ↦ ½(uᵀSigv + vᵀSigu) = uᵀSigv  by symmetry [hSymm];
  -- ③ evaluate at (eᵢ,eⱼ) ⇒ Sigᵢⱼ; `ring_nf` + `simp [quadForm, Pi.single]`.
  --
  -- 卡点：Mathlib 中 `iteratedFDeriv` 对显式二次多项式的二阶导没有现成的
  -- "等于双线性形式" 引理。需要手动展开 `iteratedFDeriv` 的定义（递归 fderiv），
  -- 对 `quadForm` 求一阶导得到线性映射，再求二阶导得到常双线性映射，
  -- 然后代入 `Pi.single` 并化简。此过程涉及大量 `Finset.sum` 的展开与
  -- `Pi.single` 的求值，目前未能自动完成。
  sorry

/-- `quadForm` is degree-2: all Fréchet derivatives of order ≥ 3 vanish identically. -/
lemma quadForm_high_deriv_zero
    (Sig : Matrix (Fin 4) (Fin 4) ℝ) (n : ℕ) (hn : 3 ≤ n) :
    iteratedFDeriv ℝ n (fun t : Fin 4 → ℝ => quadForm Sig t) 0 = 0 := by
  -- Faa di Bruno for a polynomial of degree 2 ⇒ ∂^n = 0 for n ≥ 3.
  -- Lean 路线：用 `iteratedFDeriv` 的多线性性 + 逐坐标偏导在 0 处 2 阶以上为 0，
  -- 或直接把 quadForm 写成 `ContinuousLinearMap`/双线性并 `rfl`-级消项。
  --
  -- 卡点：需要证明对任意 n ≥ 3，`iteratedFDeriv ℝ n (quadForm Sig) 0` 作为
  -- n 重线性映射恒为零。Mathlib 没有 "多项式次数 < n 则 n 阶导为零" 的通用引理
  -- 直接适用于 `iteratedFDeriv`。需要手动归纳 n 或利用 `quadForm` 的显式求和形式
  -- 逐阶求导，但 `iteratedFDeriv` 的递归定义使得高阶展开非常繁琐。
  sorry

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
  -- 卡点：这是整个证明的核心难点。需要：
  -- 1. 应用 Faa di Bruno 公式（或 Bell 多项式）展开 `iteratedFDeriv (exp ∘ quadForm)`；
  -- 2. 利用 `quadForm_high_deriv_zero` 消去所有含 3 阶或更高 `quadForm` 导数的项；
  -- 3. 利用 `quadForm_second_partial` 将二阶导数替换为 `Sig` 的矩阵元；
  -- 4. 对 4 个方向 `e₀,e₁,e₂,e₃` 枚举所有 set partitions，只有 2+2 型存活；
  -- 5. 化简得到 `isserlisRHS Sig`。
  -- Mathlib 中没有现成的 Faa di Bruno 引理适用于 `iteratedFDeriv`，
  -- 需要手动构造或引用外部结果。目前无法自动完成。
  sorry

/-- **Isserlis, n=4** (lemma [L15]; GR/Janson; the algebra core of S7).  For a
symmetric covariance `Sig`, the fourth mgf-derivative equals the matching sum. -/
theorem isserlis_4pt (Sig : Matrix (Fin 4) (Fin 4) ℝ) (hSymm : Sig.IsSymm) :
    fourthMoment Sig = isserlisRHS Sig := by
  -- `fourthMoment` is definitionally the mgf 4-th mixed derivative.
  exact mgf_deriv_exp_chain Sig hSymm

end S6