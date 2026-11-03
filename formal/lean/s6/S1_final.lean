import Mathlib.Analysis.Distribution.FourierMultiplier
import S6Isserlis.S3
import S6Isserlis.S1weak_draft

/-!
# S1 完全形式化 — 最终定理（自足,无假设泄漏）

节点位置（节点图）：
  `S1_DISTRIBUTION_IDENTIFICATION`（唯一 PROVED 的证明层节点,纸面 PROVED
  2026-09-01,critic ACCEPT）
  - 依赖（requires）：仅 `SCHWINGER_FUNCTIONS`（LITERATURE_SUPPORTED,提供已核验的
    Schwinger 参数积分输入）——不依赖 S3 的证明;
  - 被依赖：`S3_DISTRIBUTION`（S3 的 A0 由 S1 独立承担,A1–A3 留在 S3）。

本文件在 `S1weak_draft`（35 lemmas 全部闭合）之上,给出 S1 的自足最终定理:
`hq`（Green 乘子的温和增长性）不再作为假设出现,而是由 `S3` 中已注册的
`q_real_hasTemperateGrowth`（reuse_modules 白名单内）直接供给。
红线：证明体未使用任何 S6 `green_identity`（`s1_no_downstream_green_identity`）。

分析链（全部在 S1/S1a/S1weak_draft 内,无 sorry）：
  posKernel（= Schwinger aIntegral,定义性对象）
  → heatDual（热核对偶）→ x_t_fubini / p_t_fubini（双重 Fubini）
  → q_schwinger（∫₀^∞ e^{−(m²+(2π)²‖p‖²)t} dt = q(p)）
  → greenDistribution_apply（⟨𝓕⁻[q], φ⟩ = ∫ q(p) 𝓕⁻φ(p) dp）
-/

open SchwartzMap MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace
open Laplacian LineDeriv Real

noncomputable section

namespace S6Isserlis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [(volume : Measure V).HasTemperateGrowth]

/-- `HasTemperateGrowth` of the ℂ-coerced Green multiplier, closed from the
    ℝ-valued `S6Isserlis.S3.q_real_hasTemperateGrowth` (registered reuse module)
    via the `fun_prop` machinery for `HasTemperateGrowth` (which understands the
    ℝ→ℂ embedding). -/
lemma s1_q_growth (m : ℝ) (hm : 0 < m) :
    (fun p : V ↦ (((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth := by
  have hq : (fun p : V ↦ ((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ)).HasTemperateGrowth :=
    q_real_hasTemperateGrowth m hm
  fun_prop

/-- **S1 分布恒等式（完全形式化,自足）.**
    For `m > 0` in dimension 4, the position kernel `c_m` defined by the
    Schwinger parameter integral pairs with the inverse-Fourier Green
    distribution on all of `𝓢(V, ℂ)`:

        ∫ c_m(x) φ(x) dx = ⟨𝓕⁻[1/(m²+(2π)²‖·‖²)], φ⟩

    The temperate-growth side condition is closed by
    `S6Isserlis.S3.q_real_hasTemperateGrowth` (registered reuse module);
    no assumption about `q` leaks into the statement.
    (Pointwise `K₁` closed form `mK₁(mr)/(4π²r)` is a documented remark:
    Mathlib has no `BesselK`; the equality holds at the definitional level.) -/
theorem s1_distribution_identity (m : ℝ) (hm : 0 < m)
    (hfin : Module.finrank ℝ V = 4) (φ : 𝓢(V, ℂ)) :
    (∫ v : V, (posKernel m v : ℂ) * φ v) =
      (greenDistribution m hm (s1_q_growth m hm)) φ := by
  -- `s1_weak_form` with the same `hq` witness proves exactly our goal
  -- statement (modulo definitional unfolding of `posKernel` and proof
  -- irrelevance for the Prop argument of `greenDistribution`).
  exact s1_weak_form m hm hfin φ (s1_q_growth m hm)

end S6Isserlis
