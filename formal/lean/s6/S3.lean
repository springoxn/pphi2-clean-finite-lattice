import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# S3 formalized: the Euclidean Green function identity

Statement (see `proofs/s3_green_distribution.md` and
`proofs/s3_assumptions_closure.md`): for `m > 0` and `V` a finite dimensional
real inner product space,

  (Δ − m²) · ℱ⁻¹[q] = −δ₀     in 𝓢'(V, ℂ),

with `q(p) = 1 / (m² + (2π)² ‖p‖²)` and `δ₀` the Dirac measure at `0`.

Convention note: `SchwartzMap`'s Fourier transform is (2π)-normalized
(kernel `e^{−2πi⟨x, ·⟩}`), so `laplacian_eq_fourierMultiplierCLM` reads
`Δ f = −(2π)² • fourierMultiplierCLM (‖·‖²) f`, and the Euler–Green multiplier
carries the matching `(2π)²` factor.  With this normalization the constant is
clean: `∫ (𝓕⁻ ψ)(p) dp = ψ(0)`.
-/

open SchwartzMap MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace
open Laplacian LineDeriv Real

noncomputable section

namespace S6Isserlis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [(volume : Measure V).HasTemperateGrowth]

/-- The ℝ-action on a ℂ-module element equals the coerced ℂ-action
(points to the `Module.complexToReal` compatibility). -/
lemma rceq (a : ℝ) (X : 𝓢'(V, ℂ)) : a • X = (a : ℂ) • X := by
  ext ψ
  rfl

/-- (↑x : ℂ) squared is the coerced square (coe/pow interchange). -/
lemma ofReal_pow_two (x : ℝ) : (x : ℂ) ^ 2 = ↑(x ^ 2) := by
  rw [Complex.ofReal_pow]

/-- `q(p) = 1/(m² + (2π)² ‖p‖²)` as a complex function (coerced from ℝ). -/
def greenMultiplier (m : ℝ) (p : V) : ℂ :=
  (((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ) : ℂ)

/-- `q̄(p) = m² + (2π)² ‖p‖²` as a complex function. -/
def greenDenominator (m : ℝ) (p : V) : ℂ :=
  ((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2 : ℝ) : ℂ)

lemma greenDenominator_mul_greenMultiplier (m : ℝ) (hm : 0 < m) :
    (fun p : V ↦ greenDenominator m p * greenMultiplier m p) = (fun _ : V ↦ (1 : ℂ)) := by
  funext p
  have h : (m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2 : ℝ) ≠ 0 := by
    have hmpos : 0 < (m ^ 2 : ℝ) := sq_pos_of_pos hm
    have hnneg : 0 ≤ (2 * π) ^ 2 * ‖p‖ ^ 2 := by
      exact mul_nonneg (sq_nonneg (2 * π : ℝ)) (sq_nonneg ‖p‖)
    exact ne_of_gt (add_pos_of_pos_of_nonneg hmpos hnneg)
  rw [greenMultiplier, greenDenominator, ← Complex.ofReal_mul, mul_inv_cancel₀ h,
    Complex.ofReal_one]

/-- The real-valued `q̄` is smooth and temperate (`fun_prop` keeps the bookkeeping). -/
lemma greenDenominator_hasTemperateGrowth (m : ℝ) :
    (fun p : V ↦ (m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2 : ℝ)).HasTemperateGrowth := by
  fun_prop

/-- The real-valued Green multiplier `q = 1/q̄` is smooth and temperate.
Extracted with `HasTemperateGrowth` closed under multiplication/composition and
`hasTemperateGrowth_one_add_norm_sq_rpow` (Bessel potential), using
`q(p) = m⁻² · (1 + ‖((2π)/m)·p‖²)⁻¹` (`rpow (-1) = inv`).  The paper check is
`proofs/os4_free_scalar_regularity.md` §1 (L1). -/
theorem q_real_hasTemperateGrowth (m : ℝ) (hm : 0 < m) :
    (fun p : V ↦ ((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ)).HasTemperateGrowth := by
  -- q(p) = m⁻² · (1 + ‖(2π/m)·p‖²)^(-1)  (rpow makes the Bessel-potential lemma applicable)
  let t : ℝ := (2 * π) / m
  have hlin : (fun p : V ↦ t • p).HasTemperateGrowth := by
    exact ((t • (ContinuousLinearMap.id ℝ V : V →L[ℝ] V)).hasTemperateGrowth)
  have hrpow : (fun x : V ↦ (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow (H := V) (r := (-1 : ℝ))
  have hstep : (fun p : V ↦ (1 + ‖t • p‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth :=
    hrpow.comp hlin
  have hconst : (fun _ : V ↦ ((m ^ 2)⁻¹ : ℝ)).HasTemperateGrowth :=
    Function.HasTemperateGrowth.const ((m ^ 2)⁻¹ : ℝ)
  have hq' : (fun p : V ↦ ((m ^ 2)⁻¹ : ℝ) * (1 + ‖t • p‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth :=
    hconst.mul hstep
  convert hq' using 1
  ext p
  dsimp [t]
  simp [Real.rpow_neg_one]
  simp [norm_smul, mul_pow, Real.norm_eq_abs]
  rw [abs_of_pos Real.pi_pos, abs_of_pos hm]
  field_simp [ne_of_gt hm]

/-- The Green function as a tempered distribution: `G = 𝓕⁻[q]`. -/
def greenDistribution (m : ℝ) (hm : 0 < m)
    (hq : (fun p : V ↦ (((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth) :
    𝓢'(V, ℂ) :=
  𝓕⁻ (hq.toTemperedDistribution (volume : Measure V))

/-- Inversion at a point on the test-function side: with the (2π)-normalized
Schwartz Fourier transform, `∫ (𝓕⁻ ψ)(p) dp = ψ(0)`. -/
lemma fourierInvIntegral_eval_zero (ψ : 𝓢(V, ℂ)) :
    (∫ p : V, 𝓕⁻ ψ p) = ψ 0 := by
  calc
    (∫ p : V, 𝓕⁻ ψ p) =
        (∫ v : V, Complex.exp (↑(-2 * π * inner ℝ v 0) * Complex.I) • 𝓕⁻ ψ v) := by
      congr 1
      funext p
      simp [inner_zero_right]
    _ = (𝓕 (𝓕⁻ ψ)) 0 := by
      exact (Real.fourier_eq' (fun v : V ↦ (𝓕⁻ ψ) v) 0).symm
    _ = ψ 0 := by
      exact congr_fun (congrArg (fun f : 𝓢(V, ℂ) ↦ (f : V → ℂ))
        (FourierTransform.fourier_fourierInv_eq ψ)) 0

/-- The inverse Fourier transform of the constant function `1` is the Dirac
distribution at `0`. -/
lemma fourierInv_const_one_eq_dirac :
    𝓕⁻ (Function.HasTemperateGrowth.toTemperedDistribution
          (volume : Measure V) (by fun_prop : (fun _ : V ↦ (1 : ℂ)).HasTemperateGrowth)) =
      (Measure.dirac 0).toTemperedDistribution := by
  ext ψ
  let h1 : (fun _ : V ↦ (1 : ℂ)).HasTemperateGrowth := by fun_prop
  -- proof irrelevance: the inline witness is replaced by h1 (both proofs of a Prop)
  change (𝓕⁻ (Function.HasTemperateGrowth.toTemperedDistribution (volume : Measure V) h1)) ψ =
    (Measure.dirac 0).toTemperedDistribution ψ
  change (Function.HasTemperateGrowth.toTemperedDistribution (volume : Measure V) h1) (𝓕⁻ ψ) =
    (Measure.dirac 0).toTemperedDistribution ψ
  change (∫ p : V, (𝓕⁻ ψ p) • (1 : ℂ)) = (∫ x : V, ψ x ∂ (Measure.dirac 0))
  simp only [smul_eq_mul, mul_one]
  rw [fourierInvIntegral_eval_zero]
  simp

/-- Operator identity: the Klein–Gordon operator on `G` reduces to the
negative Fourier multiplier with `q̄ = m² + (2π)²‖·‖²`:
`(Δ − m²)G = − M(q̄)G`. -/
lemma green_laplacian_minus_mass (m : ℝ) (hm : 0 < m)
    (hq : (fun p : V ↦ (((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth) :
    Δ (greenDistribution m hm hq) - (m ^ 2) • greenDistribution m hm hq =
      - TemperedDistribution.fourierMultiplierCLM ℂ (fun p : V ↦ greenDenominator m p)
          (greenDistribution m hm hq : 𝓢'(V, ℂ)) := by
  let G : 𝓢'(V, ℂ) := greenDistribution m hm hq
  let g1 : V → ℂ := fun x ↦ Complex.ofReal (‖x‖ ^ 2)
  let g0 : V → ℂ := fun x ↦ (↑(2 * π) : ℂ) ^ 2 • g1 x
  let g2 : V → ℂ := fun _ ↦ (↑(m ^ 2) : ℂ)
  have hg1 : (fun x : V ↦ Complex.ofReal (‖x‖ ^ 2)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_norm_sq (H := V))
  have hg2 : (fun _ : V ↦ (↑(m ^ 2) : ℂ)).HasTemperateGrowth := by fun_prop
  have hconP : (fun _ : V ↦ ((↑(2 * π) : ℂ) ^ 2 : ℂ)).HasTemperateGrowth := by fun_prop
  have hg0 : ((fun x : V ↦ (↑(2 * π) : ℂ) ^ 2 • Complex.ofReal (‖x‖ ^ 2) : V → ℂ)).HasTemperateGrowth := by
    have hmul : ((fun x : V ↦ Complex.ofReal (‖x‖ ^ 2) * (↑(2 * π) : ℂ) ^ 2 : V → ℂ)).HasTemperateGrowth :=
      Function.HasTemperateGrowth.mul hg1 hconP
    convert hmul using 1
    ext x
    simp [smul_eq_mul, mul_comm]
  --  Δ G = −(2π)² • M(‖·‖²) G
  have hΔ : Δ G = (-(2 * π) ^ 2) •
      TemperedDistribution.fourierMultiplierCLM ℂ (fun x : V ↦ Complex.ofReal (‖x‖ ^ 2)) G := by
    dsimp [G]
    simpa using (TemperedDistribution.laplacian_eq_fourierMultiplierCLM (E := V) (F := ℂ) (f := greenDistribution m hm hq))
  --  m² • G = M(const m²) G
  have hm2 : (↑(m ^ 2) : ℂ) • G = TemperedDistribution.fourierMultiplierCLM ℂ (fun _ : V ↦ (↑(m ^ 2) : ℂ)) G := by
    have hc : TemperedDistribution.fourierMultiplierCLM ℂ (fun _ : V ↦ (↑(m ^ 2) : ℂ)) G = (↑(m ^ 2) : ℂ) • G := by
      simpa using congrArg (fun L : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) ↦ L G)
        (TemperedDistribution.fourierMultiplierCLM_const (F := ℂ) (c := (↑(m ^ 2) : ℂ)))
    exact hc.symm
  --  −(2π)² • M(g1) = −M(g0)   (with g0 = (2π)² • g1; fourierMultiplierCLM_smul)
  have hsm : (↑(-((2 * π : ℝ) ^ 2)) : ℂ) • TemperedDistribution.fourierMultiplierCLM ℂ g1 G =
      - TemperedDistribution.fourierMultiplierCLM ℂ g0 G := by
    have hM0 : TemperedDistribution.fourierMultiplierCLM ℂ g0 G =
        (↑(2 * π) : ℂ) ^ 2 • TemperedDistribution.fourierMultiplierCLM ℂ g1 G :=
      congrArg (fun L : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) ↦ L G)
        (TemperedDistribution.fourierMultiplierCLM_smul hg1 ((↑(2 * π) : ℂ) ^ 2))
    rw [hM0]
    simp [Complex.ofReal_neg, Complex.ofReal_pow]
  --  M(g0) + M(g2) = M(g0 + g2)       (fourierMultiplierCLM_sum, two elements)
  have hsum : TemperedDistribution.fourierMultiplierCLM ℂ g0 G +
        TemperedDistribution.fourierMultiplierCLM ℂ g2 G =
      TemperedDistribution.fourierMultiplierCLM ℂ (fun p : V ↦ g0 p + g2 p) G := by
    have hsumCLM :
        TemperedDistribution.fourierMultiplierCLM ℂ g0 +
            TemperedDistribution.fourierMultiplierCLM ℂ g2 =
          TemperedDistribution.fourierMultiplierCLM ℂ (fun p : V ↦ g0 p + g2 p) := by
      have hsum' := TemperedDistribution.fourierMultiplierCLM_sum (F := ℂ)
        (s := ({0, 1} : Finset (Fin 2)))
        (g := fun i : Fin 2 ↦ if i = 0 then g0 else g2)
        (hg := by
          intro i hi
          fin_cases i
          · dsimp [g0, g1, g2]
            exact hg0
          · dsimp [g0, g1, g2]
            exact hg2)
      simpa [Finset.sum_pair, add_comm, add_left_comm, add_assoc] using hsum'.symm
    simpa [Pi.add_apply] using
      congrArg (fun L : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) ↦ L G) hsumCLM
  --  q̄ = g0 + g2 pointwise
  have hqb : (fun p : V ↦ g0 p + g2 p) = greenDenominator m := by
    funext p
    dsimp [g0, g1, g2, greenDenominator]
    simp [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_neg, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm]
  -- assemble:  ΔG − m²G = −(M(g0)G + M(g2)G) = −M(q̄)G
  have hsmulℝ : (m ^ 2) • G = (↑(m ^ 2) : ℂ) • G := by
    calc
      (m ^ 2) • G = ↑(m ^ 2) • G := rceq (m ^ 2) G
      _ = (↑(m ^ 2) : ℂ) • G := rfl
  have hsmulℝ2 : (-(2 * π : ℝ) ^ 2) • TemperedDistribution.fourierMultiplierCLM ℂ g1 G =
      (↑(-((2 * π : ℝ) ^ 2)) : ℂ) • TemperedDistribution.fourierMultiplierCLM ℂ g1 G := by
    calc
      (-(2 * π : ℝ) ^ 2) • TemperedDistribution.fourierMultiplierCLM ℂ g1 G =
          ↑(-((2 * π : ℝ) ^ 2)) • TemperedDistribution.fourierMultiplierCLM ℂ g1 G :=
        rceq (-(2 * π : ℝ) ^ 2) (TemperedDistribution.fourierMultiplierCLM ℂ g1 G)
      _ = (↑(-((2 * π : ℝ) ^ 2)) : ℂ) • TemperedDistribution.fourierMultiplierCLM ℂ g1 G := rfl
  rw [hsmulℝ, hΔ, hm2, hsmulℝ2, hsm]
  rw [show -TemperedDistribution.fourierMultiplierCLM ℂ g0 G -
        TemperedDistribution.fourierMultiplierCLM ℂ g2 G =
      -(TemperedDistribution.fourierMultiplierCLM ℂ g0 G + TemperedDistribution.fourierMultiplierCLM ℂ g2 G) by abel]
  rw [hsum, hqb]

/-- The multiplier `q̄` applied to the Green function is the inverse Fourier
transform of the constant function `1`: `M(q̄)G = 𝓕⁻(1-dist)`. -/
lemma greenMultiplier_eq_fourierInv_one (m : ℝ) (hm : 0 < m)
    (hq : (fun p : V ↦ (((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth) :
    TemperedDistribution.fourierMultiplierCLM ℂ (fun p : V ↦ greenDenominator m p)
        (greenDistribution m hm hq : 𝓢'(V, ℂ)) =
      𝓕⁻ ((Function.HasTemperateGrowth.toTemperedDistribution (volume : Measure V)
            (by fun_prop : (fun _ : V ↦ (1 : ℂ)).HasTemperateGrowth)) : 𝓢'(V, ℂ)) := by
  ext ψ
  let S : 𝓢'(V, ℂ) := hq.toTemperedDistribution (volume : Measure V)
  let qhat : V → ℂ := greenMultiplier m
  let qbar : V → ℂ := fun p ↦ greenDenominator m p
  -- M(q̄)(𝓕⁻S) = 𝓕⁻(q̄ • S) (definitional), then 𝓕⁻(q̄•S) ψ = (q̄•S)(𝓕⁻ ψ)
  rw [TemperedDistribution.fourierMultiplierCLM_apply]
  rw [TemperedDistribution.fourierInv_apply]
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  change 𝓕 (𝓕⁻ (hq.toTemperedDistribution (volume : Measure V))) (SchwartzMap.smulLeftCLM ℂ qbar (𝓕⁻ ψ)) =
    (Function.HasTemperateGrowth.toTemperedDistribution (volume : Measure V)
      (by fun_prop : (fun _ : V ↦ (1 : ℂ)).HasTemperateGrowth)) (𝓕⁻ ψ)
  -- 𝓕 (𝓕⁻ T) φ = T (𝓕⁻ (𝓕 φ)) (defeq by fourier_apply/fourierInv_apply), then Schwartz-level inversion
  rw [TemperedDistribution.fourier_apply]
  rw [TemperedDistribution.fourierInv_apply]
  rw [FourierTransform.fourierInv_fourier_eq]
  change S (SchwartzMap.smulLeftCLM ℂ qbar (𝓕⁻ ψ)) =
    (Function.HasTemperateGrowth.toTemperedDistribution (volume : Measure V)
      (by fun_prop : (fun _ : V ↦ (1 : ℂ)).HasTemperateGrowth)) (𝓕⁻ ψ)
  -- unfold both sides to their integral form (test · multiplier convention)
  have hqbart : (fun p : V ↦ greenDenominator m p).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (greenDenominator_hasTemperateGrowth m)
  dsimp [S]
  change (∫ x : V, ((smulLeftCLM ℂ qbar) (𝓕⁻ ψ)) x * ↑(((m ^ 2 + (2 * π) ^ 2 * ‖x‖ ^ 2)⁻¹ : ℝ))) =
      (∫ x : V, (𝓕⁻ ψ) x * (1 : ℂ))
  -- both sides are integrals; prove the pointwise equality of the integrands and lift to the integral
  apply congrArg (MeasureTheory.integral (volume : Measure V))
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (g := qbar) (hg := hqbart) (f := 𝓕⁻ ψ) (x := x)]
  change (qbar x • (𝓕⁻ ψ) x) • qhat x = (𝓕⁻ ψ) x * (1 : ℂ)
  have hqq : qbar x * qhat x = 1 := by
    have := congrFun (greenDenominator_mul_greenMultiplier m hm) x
    simpa [qbar, qhat, greenDenominator, greenMultiplier, mul_comm] using this
  calc
    (qbar x • (𝓕⁻ ψ) x) • qhat x = (qbar x * (𝓕⁻ ψ) x) * qhat x := by simp only [smul_eq_mul]
    _ = (𝓕⁻ ψ) x * (qbar x * qhat x) := by ring
    _ = (𝓕⁻ ψ) x * (1 : ℂ) := by rw [hqq]

/-- S3 (distribution level): `(Δ − m²) G = −δ₀` in 𝓢'(V, ℂ).
The `hq` premise is the (mechanical) smoothness/boundedness check of the
multiplier function `q`; everything else is unconditional. -/
theorem green_identity (m : ℝ) (hm : 0 < m)
    (hq : (fun p : V ↦ (((m ^ 2 + (2 * π) ^ 2 * ‖p‖ ^ 2)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth) :
    Δ (greenDistribution m hm hq) - (m ^ 2) • greenDistribution m hm hq =
      - (Measure.dirac 0).toTemperedDistribution := by
  -- (Δ−m²)G = −M(q̄)G = −𝓕⁻(1-dist) = −δ₀
  rw [green_laplacian_minus_mass m hm hq]
  rw [greenMultiplier_eq_fourierInv_one m hm hq]
  rw [fourierInv_const_one_eq_dirac]

end S6Isserlis