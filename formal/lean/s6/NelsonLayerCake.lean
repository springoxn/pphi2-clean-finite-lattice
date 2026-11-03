/-
Copyright (c) 2026 AImath. All rights reserved.
Released under Apache 2.0 license.

# Nelson (V): the layer-cake engine (paper Lemma 6.1)

Abstract measure-theoretic heart of the volume-uniform Nelson estimate (V)
(proofs/pphi2_nelson_dynamical_cutoff.md, Lemma 6.1 / Lemma 4.10):

  integral e^{-qV} dmu <= 1 + integral_0^inf q e^{qM} mu{V <= -M} dM

for a probability measure mu, q > 0 and any measurable V : alpha -> R.
This file proves the interval integral it rests on, the pointwise
layer-cake inequality, its integral form, and the t0-splitting
(paper Lemma 4.10, abstract form).  The assembly into the volume-dependent
(V) comes later.

All statements are 0 sorry.
-/
import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace Pphi2Nelson

/-- **Bochner interval integral of the exponential weight.**
For `0 < b`, `∫_0^b q e^{qM} dM = e^{qb} - 1`. -/
lemma integral_exp_mul_Ioc (q b : ℝ) (hb : 0 < b) :
    ∫ M in Ioc (0 : ℝ) b, q * Real.exp (q * M) = Real.exp (q * b) - 1 := by
  have hdiff : ∀ x ∈ uIcc (0 : ℝ) b,
      HasDerivAt (fun M : ℝ => Real.exp (q * M)) (q * Real.exp (q * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun M : ℝ => q * M) q x := by
      simpa using (hasDerivAt_id x).const_mul q
    have h2 : HasDerivAt (fun M : ℝ => Real.exp (q * M)) (Real.exp (q * x) * q) x :=
      h1.exp
    rw [mul_comm (Real.exp (q * x)) q] at h2
    exact h2
  have hint : IntervalIntegrable (fun M : ℝ => q * Real.exp (q * M)) volume 0 b :=
    (by fun_prop : Continuous (fun M : ℝ => q * Real.exp (q * M))).intervalIntegrable 0 b
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hdiff hint
  rw [← intervalIntegral.integral_of_le hb.le]
  simpa using key

/-- **LIntegral of the exponential weight over `Ioc 0 b`.** -/
lemma lintegral_exp_Ioc (q b : ℝ) (hq : 0 < q) (hb : 0 < b) :
    ∫⁻ M in Ioc (0 : ℝ) b, ENNReal.ofReal (q * Real.exp (q * M)) =
      ENNReal.ofReal (Real.exp (q * b) - 1) := by
  have hInt : IntegrableOn (fun M : ℝ => q * Real.exp (q * M)) (Ioc (0 : ℝ) b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp
      ((by fun_prop :
        Continuous (fun M : ℝ => q * Real.exp (q * M))).intervalIntegrable 0 b)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (ae_of_all _ (fun M => mul_nonneg hq.le (Real.exp_nonneg _))),
    integral_exp_mul_Ioc q b hb]

/-- **Pointwise layer-cake inequality.**
For `q > 0` and every real `x`,
`e^{-qx} ≤ 1 + ∫_0^∞ q e^{qM} · 1_{M ≤ -x} dM` on `ℝ≥0∞`. -/
lemma exp_neg_le_layercake (q : ℝ) (hq : 0 < q) (x : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * x))) ≤
      1 + ∫⁻ M in Ioi (0 : ℝ),
        ENNReal.ofReal (q * Real.exp (q * M)) *
          (Set.Iic (-x)).indicator (fun _ => (1 : ℝ≥0∞)) M := by
  rcases lt_or_ge x 0 with hx | hx
  · -- Case `x < 0` (`hx : x < 0`).
    have hb : 0 < -x := neg_pos.mpr hx
    have hsub : Set.Ioc (0 : ℝ) (-x) ⊆ Ioi (0 : ℝ) := fun _ h => h.1
    have hset : (Set.Ioc (0 : ℝ) (-x)) ∩ Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) (-x) := by
      ext M; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]; tauto
    have hcongr :
        (∫⁻ M in Ioi (0 : ℝ),
          ENNReal.ofReal (q * Real.exp (q * M)) *
            (Set.Iic (-x)).indicator (fun _ => (1 : ℝ≥0∞)) M) =
          ∫⁻ M in Ioi (0 : ℝ),
            (Set.Ioc (0 : ℝ) (-x)).indicator
              (fun M => ENNReal.ofReal (q * Real.exp (q * M))) M := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro M hM
      rw [Set.mem_Ioi] at hM
      by_cases hMx : M ≤ -x
      · have h1 : M ∈ Set.Iic (-x) := Set.mem_Iic.mpr hMx
        have h2 : M ∈ Set.Ioc (0 : ℝ) (-x) := ⟨hM, hMx⟩
        simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2, mul_one]
      · have h1 : M ∉ Set.Iic (-x) := fun h => hMx (Set.mem_Iic.mp h)
        have h2 : M ∉ Set.Ioc (0 : ℝ) (-x) := fun h => hMx h.2
        simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, mul_zero]
    rw [hcongr, setLIntegral_indicator (s := Set.Ioc (0 : ℝ) (-x))
        (f := fun M => ENNReal.ofReal (q * Real.exp (q * M))) measurableSet_Ioc,
      hset, lintegral_exp_Ioc q (-x) hq hb]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num)
      (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hq.le hb.le)))]
    apply ENNReal.ofReal_le_ofReal
    have harg : q * -x = -(q * x) := by ring
    rw [harg]; linarith
  · -- Case `0 ≤ x` (`hx : 0 ≤ x`): the integral vanishes, RHS `= 1 ≥ e^{-qx}`.
    have hzero :
        (∫⁻ M in Ioi (0 : ℝ),
          ENNReal.ofReal (q * Real.exp (q * M)) *
            (Set.Iic (-x)).indicator (fun _ => (1 : ℝ≥0∞)) M) = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ioi
      intro M hM
      rw [Set.mem_Ioi] at hM
      have h1 : M ∉ Set.Iic (-x) := by rw [Set.mem_Iic]; linarith
      simp only [Set.indicator_of_notMem h1, mul_zero, Pi.zero_apply]
    rw [hzero, add_zero]
    apply ENNReal.ofReal_le_one.mpr
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq.le hx))

variable {α : Type*} [MeasurableSpace α]

/-- **Layer-cake inequality against a probability measure (paper Lemma 6.1).**
For a probability measure `μ`, `q > 0` and a measurable `V : α → ℝ`,
`∫ e^{-qV} dμ ≤ 1 + ∫_0^∞ q e^{qM} μ{V ≤ -M} dM` (in `ℝ≥0∞`). -/
theorem lintegral_exp_neg_le (μ : Measure α) [IsProbabilityMeasure μ]
    (q : ℝ) (hq : 0 < q) (V : α → ℝ) (hV : Measurable V) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(q * V ω))) ∂μ ≤
      1 + ∫⁻ M in Ioi (0 : ℝ),
        ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M} := by
  have hpoint : ∀ ω, ENNReal.ofReal (Real.exp (-(q * V ω))) ≤
      1 + ∫⁻ M in Ioi (0 : ℝ),
        ENNReal.ofReal (q * Real.exp (q * M)) *
          (Set.Iic (-(V ω))).indicator (fun _ => (1 : ℝ≥0∞)) M :=
    fun ω => exp_neg_le_layercake q hq (V ω)
  have hs : MeasurableSet {p : α × ℝ | p.2 ≤ -(V p.1)} :=
    measurableSet_le measurable_snd ((hV.comp measurable_fst).neg)
  have hmeas : Measurable (Function.uncurry (fun ω M => ENNReal.ofReal (q * Real.exp (q * M)) *
      (Set.Iic (-(V ω))).indicator (fun _ => (1 : ℝ≥0∞)) M)) := by
    apply Measurable.mul
    · fun_prop
    · convert Measurable.indicator
        (measurable_const : Measurable (fun _ : α × ℝ => (1 : ℝ≥0∞))) hs using 1
      funext p
      by_cases h : p.2 ≤ -(V p.1)
      · rw [Set.indicator_of_mem (show p.2 ∈ Set.Iic (-(V p.1)) from h),
          Set.indicator_of_mem (show p ∈ {q : α × ℝ | q.2 ≤ -(V q.1)} from h)]
      · rw [Set.indicator_of_notMem (show p.2 ∉ Set.Iic (-(V p.1)) from
            fun hx => h (Set.mem_Iic.mp hx)),
          Set.indicator_of_notMem (show p ∉ {q : α × ℝ | q.2 ≤ -(V q.1)} from
            fun hx => h (show p.2 ≤ -(V p.1) from hx))]
  have hmeas_ind : ∀ M : ℝ, Measurable (fun ω : α =>
      (Set.Iic (-(V ω))).indicator (fun _ => (1 : ℝ≥0∞)) M) := by
    intro M
    convert Measurable.indicator (measurable_const : Measurable (fun _ : α => (1 : ℝ≥0∞)))
      (measurableSet_le hV measurable_const) using 1
    funext ω
    by_cases h : M ≤ -(V ω)
    · have h1 : M ∈ Set.Iic (-(V ω)) := h
      have h2 : ω ∈ {a : α | V a ≤ -M} := by simp only [Set.mem_setOf_eq]; linarith
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · have h1 : M ∉ Set.Iic (-(V ω)) := fun hx => h (Set.mem_Iic.mp hx)
      have h2 : ω ∉ {a : α | V a ≤ -M} := by simp only [Set.mem_setOf_eq]; linarith
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have hswap := lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ)))
    (f := fun ω M => ENNReal.ofReal (q * Real.exp (q * M)) *
      (Set.Iic (-(V ω))).indicator (fun _ => (1 : ℝ≥0∞)) M)
    hmeas.aemeasurable
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-(q * V ω))) ∂μ
      ≤ ∫⁻ ω, (1 + ∫⁻ M in Ioi (0 : ℝ),
          ENNReal.ofReal (q * Real.exp (q * M)) *
            (Set.Iic (-(V ω))).indicator (fun _ => (1 : ℝ≥0∞)) M) ∂μ :=
        lintegral_mono hpoint
    _ = 1 + ∫⁻ ω, (∫⁻ M in Ioi (0 : ℝ),
          ENNReal.ofReal (q * Real.exp (q * M)) *
            (Set.Iic (-(V ω))).indicator (fun _ => (1 : ℝ≥0∞)) M) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_one, measure_univ]
    _ = 1 + ∫⁻ M in Ioi (0 : ℝ), ENNReal.ofReal (q * Real.exp (q * M)) *
          (∫⁻ ω, (Set.Iic (-(V ω))).indicator (fun _ => (1 : ℝ≥0∞)) M ∂μ) := by
        rw [hswap]
        apply congrArg (fun t => 1 + t)
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro M _
        simp only []
        rw [lintegral_const_mul _ (hmeas_ind M)]
    _ = 1 + ∫⁻ M in Ioi (0 : ℝ),
          ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M} := by
        apply congrArg (fun t => 1 + t)
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro M _
        simp only []
        congr 1
        rw [← lintegral_indicator_one (measurableSet_le hV measurable_const)]
        apply lintegral_congr
        intro ω
        by_cases h : M ≤ -(V ω)
        · have h1 : M ∈ Set.Iic (-(V ω)) := h
          have h2 : ω ∈ {a : α | V a ≤ -M} := by simp only [Set.mem_setOf_eq]; linarith
          rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          rfl
        · have h1 : M ∉ Set.Iic (-(V ω)) := fun hx => h (Set.mem_Iic.mp hx)
          have h2 : ω ∉ {a : α | V a ≤ -M} := by simp only [Set.mem_setOf_eq]; linarith
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- **`t₀`-splitting of the layer-cake bound (paper Lemma 4.10, abstract form).**
Given a tail hypothesis `μ{V ≤ -M} ≤ ψ M` for `M ≥ t₀` (the smooth-cutoff
regime) and the trivial `μ ≤ 1` on `[0, t₀]`, the layer-cake bound splits as
`∫ e^{-qV} dμ ≤ e^{q t₀} + ∫_{t₀}^∞ q e^{qM} ψ(M) dM` (in `ℝ≥0∞`). -/
theorem lintegral_exp_neg_le_split (μ : Measure α) [IsProbabilityMeasure μ]
    (q : ℝ) (hq : 0 < q) (V : α → ℝ) (hV : Measurable V)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (ψ : ℝ → ℝ≥0∞)
    (htail : ∀ M, t₀ ≤ M → μ {ω | V ω ≤ -M} ≤ ψ M) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(q * V ω))) ∂μ ≤
      ENNReal.ofReal (Real.exp (q * t₀)) +
        ∫⁻ M in Ioi t₀, ENNReal.ofReal (q * Real.exp (q * M)) * ψ M := by
  have h0 := lintegral_exp_neg_le μ q hq V hV
  have hmeasure_le_one : ∀ s : Set α, μ s ≤ 1 := fun s => by
    rw [← measure_univ (μ := μ)]
    exact measure_mono (Set.subset_univ s)
  have hunion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) t₀ ∪ Set.Ioi t₀ := by
    ext M; simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro hM
      by_cases h : M ≤ t₀
      · exact Or.inl ⟨hM, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · exact lt_of_le_of_lt ht₀ h
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) t₀) (Set.Ioi t₀) :=
    Set.disjoint_left.mpr fun a ha ha' => absurd ha.2 (not_le.mpr (Set.mem_Ioi.mp ha'))
  have hsplit :
      (∫⁻ M in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M}) =
        (∫⁻ M in Set.Ioc (0 : ℝ) t₀,
            ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M}) +
          (∫⁻ M in Set.Ioi t₀,
            ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M}) := by
    rw [hunion, lintegral_union measurableSet_Ioi hdisj]
  have hsmall :
      (∫⁻ M in Set.Ioc (0 : ℝ) t₀,
          ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M})
        ≤ ENNReal.ofReal (Real.exp (q * t₀) - 1) := by
    rcases eq_or_lt_of_le ht₀ with h | h
    · subst h; simp
    · calc (∫⁻ M in Set.Ioc (0 : ℝ) t₀,
              ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M})
          ≤ ∫⁻ M in Set.Ioc (0 : ℝ) t₀,
              ENNReal.ofReal (q * Real.exp (q * M)) * 1 :=
            setLIntegral_mono' measurableSet_Ioc
              (fun M _ => mul_le_mul_of_nonneg_left (hmeasure_le_one _) bot_le)
        _ = ∫⁻ M in Set.Ioc (0 : ℝ) t₀, ENNReal.ofReal (q * Real.exp (q * M)) := by
            simp only [mul_one]
        _ = ENNReal.ofReal (Real.exp (q * t₀) - 1) := lintegral_exp_Ioc q t₀ hq h
  have hlarge :
      (∫⁻ M in Set.Ioi t₀, ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M})
        ≤ ∫⁻ M in Set.Ioi t₀, ENNReal.ofReal (q * Real.exp (q * M)) * ψ M :=
    setLIntegral_mono' measurableSet_Ioi
      (fun M hM => mul_le_mul_of_nonneg_left (htail M (le_of_lt (Set.mem_Ioi.mp hM))) bot_le)
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-(q * V ω))) ∂μ
      ≤ 1 + ∫⁻ M in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M} := h0
    _ = 1 + ((∫⁻ M in Set.Ioc (0 : ℝ) t₀,
            ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M}) +
          (∫⁻ M in Set.Ioi t₀,
            ENNReal.ofReal (q * Real.exp (q * M)) * μ {ω | V ω ≤ -M})) := by
        rw [hsplit]
    _ ≤ 1 + (ENNReal.ofReal (Real.exp (q * t₀) - 1) +
          ∫⁻ M in Set.Ioi t₀, ENNReal.ofReal (q * Real.exp (q * M)) * ψ M) :=
        add_le_add (le_refl 1) (add_le_add hsmall hlarge)
    _ = ENNReal.ofReal (Real.exp (q * t₀)) +
          ∫⁻ M in Set.Ioi t₀, ENNReal.ofReal (q * Real.exp (q * M)) * ψ M := by
        rw [← add_assoc]
        congr 1
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num)
            (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hq.le ht₀)))]
        congr 1
        ring

end Pphi2Nelson
