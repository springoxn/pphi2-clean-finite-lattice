import AImathPPhi2Clean.PeriodicH1Completion
import AImathPPhi2Clean.PeriodicTorusWeakResolvent
import AImathPPhi2Clean.PeriodicMassiveEnergy
import AImathPPhi2Clean.PeriodicTorusModeDerivative

noncomputable section
open scoped Topology BigOperators InnerProductSpace lp
namespace Pphi2Clean.Continuum

/-- The inclusion of the completed energy space in the actual periodic L2. -/
def periodicH1Value (d : ℕ) (L mass : ℝ) (hmass : 0 < mass) :
    MassiveEnergy (Fin d → ℤ) →L[ℂ] PeriodicL2 d :=
  (periodicMassiveEmbedding d L mass hmass).liftCLM (periodicFourierHilbertBasis d)

/-- Physical coordinate gradients, with the factor 1/L in each frequency. -/
def periodicH1Gradient (d : ℕ) (L mass : ℝ) (hmass : 0 < mass) (i : Fin d) :
    MassiveEnergy (Fin d → ℤ) →L[ℂ] PeriodicL2 d :=
  (periodicFourierHilbertBasis d).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (periodicEnergyGradient d L mass hmass i)

/-- The completed energy inner product is precisely the massive Dirichlet form
on physical L2 values and gradients. -/
theorem periodicH1_inner_split (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (h v : MassiveEnergy (Fin d → ℤ)) :
    ⟪h, v⟫_ℂ = (mass ^ 2 : ℝ) •
      ⟪periodicH1Value d L mass hmass h, periodicH1Value d L mass hmass v⟫_ℂ +
      ∑ i, ⟪periodicH1Gradient d L mass hmass i h,
        periodicH1Gradient d L mass hmass i v⟫_ℂ := by
  simpa only [periodicH1Value, MassiveEnergyEmbedding.liftCLM_apply,
    MassiveEnergyEmbedding.lift, periodicH1Gradient, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.inner_map_map]
    using periodicMassiveEnergy_inner_split d L mass hmass h v

theorem periodicH1_norm_sq_split (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (h : MassiveEnergy (Fin d → ℤ)) :
    ‖h‖ ^ 2 = mass ^ 2 * ‖periodicH1Value d L mass hmass h‖ ^ 2 +
      ∑ i, ‖periodicH1Gradient d L mass hmass i h‖ ^ 2 := by
  have hh := congrArg Complex.re (periodicH1_inner_split d L mass hmass h h)
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.re_sum] using hh

/-- Classical coordinate derivatives of the actual polynomial representatives. -/
theorem periodicTrigPolynomial_hasDerivAt (d : ℕ) (L : ℝ)
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (z : UnitAddTorus (Fin d)) (i : Fin d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ k ∈ S, a k * UnitAddTorus.mFourier k
      (Function.update z i ((s / L : ℝ) : UnitAddCircle)))
      (∑ k ∈ S, (a k * (periodicCoordinateFrequency d L i k : ℂ) * Complex.I) *
        UnitAddTorus.mFourier k (Function.update z i ((t / L : ℝ) : UnitAddCircle))) t := by
  simpa only [periodicCoordinateFrequency, mul_assoc] using
    hasDerivAt_trigPolynomial_physicalCoordinate L S a z i t

/-- Unweighted, arbitrary finite trigonometric polynomials and their actual
classical coordinate gradients, including an explicit derivative certificate.
This core does not depend on the mass. -/
def periodicTrigPolynomialGraph (d : ℕ) (L : ℝ) :
    Set (PeriodicL2 d × (Fin d → PeriodicL2 d)) :=
  {p | ∃ (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ),
    p = (∑ k ∈ S, a k • periodicFourierHilbertBasis d k,
      fun i => ∑ k ∈ S, (a k * (periodicCoordinateFrequency d L i k : ℂ) * Complex.I) •
        periodicFourierHilbertBasis d k) ∧
      ∀ (z : UnitAddTorus (Fin d)) (i : Fin d) (t : ℝ),
        HasDerivAt (fun s : ℝ => ∑ k ∈ S, a k * UnitAddTorus.mFourier k
          (Function.update z i ((s / L : ℝ) : UnitAddCircle)))
          (∑ k ∈ S, (a k * (periodicCoordinateFrequency d L i k : ℂ) * Complex.I) *
            UnitAddTorus.mFourier k (Function.update z i ((t / L : ℝ) : UnitAddCircle))) t}

@[simp] theorem periodicH1Value_single (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (k : Fin d → ℤ) (a : ℂ) :
    periodicH1Value d L mass hmass (lp.single 2 k a) =
      (((periodicMassiveEmbedding d L mass hmass).weight k : ℂ) * a) •
        periodicFourierHilbertBasis d k :=
  (periodicMassiveEmbedding d L mass hmass).lift_single (periodicFourierHilbertBasis d) k a

@[simp] theorem periodicH1Gradient_single (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (i : Fin d) (k : Fin d → ℤ) (a : ℂ) :
    periodicH1Gradient d L mass hmass i (lp.single 2 k a) =
      (Complex.I * (periodicCoordinateFrequency d L i k : ℂ) *
        ((periodicMassiveEmbedding d L mass hmass).weight k : ℂ) * a) •
        periodicFourierHilbertBasis d k := by
  classical
  have he : periodicEnergyGradient d L mass hmass i (lp.single 2 k a) =
      lp.single 2 k (Complex.I * (periodicCoordinateFrequency d L i k : ℂ) *
        ((periodicMassiveEmbedding d L mass hmass).weight k : ℂ) * a) := by
    apply lp.ext
    funext j
    by_cases hj : j = k
    · subst j; simp [periodicEnergyGradient_apply]
    · simp [periodicEnergyGradient_apply, lp.single_apply, hj, Ne.symm hj]
  change (periodicFourierHilbertBasis d).repr.symm
    (periodicEnergyGradient d L mass hmass i (lp.single 2 k a)) = _
  rw [he]
  have hs (c : ℂ) : (lp.single 2 k c : MassiveEnergy (Fin d → ℤ)) =
      c • (lp.single 2 k (1 : ℂ) : MassiveEnergy (Fin d → ℤ)) := by
    rw [← lp.single_smul]
    simp
  rw [hs, map_smul, HilbertBasis.repr_symm_single]

/-- Exact identification of the finite energy core with arbitrary polynomial
values and derivatives; positivity of the weights supplies the inverse map. -/
theorem periodicH1_graph_core_eq (d : ℕ) (L mass : ℝ) (hmass : 0 < mass) :
    (h1Graph d (periodicH1Value d L mass hmass) (periodicH1Gradient d L mass hmass)) ''
      finiteSupportEnergy (Fin d → ℤ) = periodicTrigPolynomialGraph d L := by
  classical
  let A := periodicMassiveEmbedding d L mass hmass
  let b := periodicFourierHilbertBasis d
  have hfinite (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
      h1Graph d (periodicH1Value d L mass hmass) (periodicH1Gradient d L mass hmass)
        (∑ k ∈ S, lp.single 2 k (c k)) =
      (∑ k ∈ S, ((A.weight k : ℂ) * c k) • b k,
        fun i => ∑ k ∈ S, (((A.weight k : ℂ) * c k) *
          (periodicCoordinateFrequency d L i k : ℂ) * Complex.I) • b k) := by
    apply Prod.ext
    · change periodicH1Value d L mass hmass (∑ k ∈ S, lp.single 2 k (c k)) = _
      simp only [map_sum, periodicH1Value_single]
      rfl
    · funext i
      change periodicH1Gradient d L mass hmass i (∑ k ∈ S, lp.single 2 k (c k)) = _
      simp only [map_sum, periodicH1Gradient_single]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring
  apply Set.Subset.antisymm
  · rintro _ ⟨h, ⟨S, hS⟩, rfl⟩
    refine ⟨S, fun k => (A.weight k : ℂ) * h k, ?_,
      periodicTrigPolynomial_hasDerivAt d L S (fun k => (A.weight k : ℂ) * h k)⟩
    have he : (∑ k ∈ S, lp.single 2 k (h k)) = h := by
      apply lp.ext
      funext k
      by_cases hk : k ∈ S
      · simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_pi_single]
        simp [hk]
      · simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_pi_single]
        simp [hk, hS k hk]
    calc
      _ = h1Graph d (periodicH1Value d L mass hmass) (periodicH1Gradient d L mass hmass)
          (∑ k ∈ S, lp.single 2 k (h k)) := congrArg _ he.symm
      _ = _ := hfinite S (fun k => h k)
  · rintro p ⟨S, a, hp, _⟩
    subst p
    let c : (Fin d → ℤ) → ℂ := fun k => a k / (A.weight k : ℂ)
    refine ⟨∑ k ∈ S, lp.single 2 k (c k), ⟨S, ?_⟩, ?_⟩
    · intro k hk
      simp only [lp.coeFn_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro r hr
      simp [lp.single_apply, ne_of_mem_of_not_mem hr hk]
    · rw [hfinite]
      have hc (k : Fin d → ℤ) : (A.weight k : ℂ) * c k = a k := by
        dsimp [c]
        exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (A.weight_pos k).ne')
      simp_rw [hc]
      rfl

/-- Periodic H1 is exactly the closed graph completion of genuine unweighted
trigonometric polynomials and their classical derivatives. -/
theorem periodicH1_graph_completion (d : ℕ) (L mass : ℝ) (hmass : 0 < mass) :
    Set.range (h1Graph d (periodicH1Value d L mass hmass)
      (periodicH1Gradient d L mass hmass)) = closure (periodicTrigPolynomialGraph d L) := by
  rw [← periodicH1_graph_core_eq d L mass hmass]
  exact massiveEnergy_graph_completion d mass _ _ (periodicH1_norm_sq_split d L mass hmass)

/-- The massive weak PDE resolvent, constructed through the Riesz solution. -/
def periodicMassiveResolvent (d : ℕ) (L mass : ℝ) (hmass : 0 < mass) :
    PeriodicL2 d →L[ℂ] PeriodicL2 d :=
  (periodicMassiveEmbedding d L mass hmass).resolventInCLM (periodicFourierHilbertBasis d)

/-- The weak PDE tests the entire completed H1 space. -/
theorem periodicMassiveResolvent_weak (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (g : PeriodicL2 d) (v : MassiveEnergy (Fin d → ℤ)) :
    let h := (periodicMassiveEmbedding d L mass hmass).solveIn (periodicFourierHilbertBasis d) g
    (mass ^ 2 : ℝ) • ⟪periodicH1Value d L mass hmass h, periodicH1Value d L mass hmass v⟫_ℂ +
      ∑ i, ⟪periodicH1Gradient d L mass hmass i h, periodicH1Gradient d L mass hmass i v⟫_ℂ =
      ⟪g, periodicH1Value d L mass hmass v⟫_ℂ := by
  dsimp only
  rw [← periodicH1_inner_split]
  exact (periodicMassiveEmbedding d L mass hmass).solveIn_weak (periodicFourierHilbertBasis d) g v

/-- A weak physical value must belong to the completed polynomial graph and
satisfy the massive Dirichlet equation against every energy test. -/
def periodicIsWeakSolution (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (g u : PeriodicL2 d) : Prop :=
  ∃ h : MassiveEnergy (Fin d → ℤ), periodicH1Value d L mass hmass h = u ∧
    ∀ v : MassiveEnergy (Fin d → ℤ),
      (mass ^ 2 : ℝ) • ⟪periodicH1Value d L mass hmass h, periodicH1Value d L mass hmass v⟫_ℂ +
        ∑ i, ⟪periodicH1Gradient d L mass hmass i h, periodicH1Gradient d L mass hmass i v⟫_ℂ =
        ⟪g, periodicH1Value d L mass hmass v⟫_ℂ

theorem periodicIsWeakSolution_iff (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (g u : PeriodicL2 d) :
    periodicIsWeakSolution d L mass hmass g u ↔
      (periodicMassiveEmbedding d L mass hmass).IsWeakValue (periodicFourierHilbertBasis d) g u := by
  unfold periodicIsWeakSolution MassiveEnergyEmbedding.IsWeakValue
  simp_rw [← periodicH1_inner_split]
  rfl

theorem periodicMassiveResolvent_existsUnique_weak (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (g : PeriodicL2 d) : ∃! u : PeriodicL2 d, periodicIsWeakSolution d L mass hmass g u := by
  simp_rw [periodicIsWeakSolution_iff]
  exact (periodicMassiveEmbedding d L mass hmass).existsUnique_weak_value
    (periodicFourierHilbertBasis d) g

theorem periodicMassiveResolvent_isWeakSolution (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (g : PeriodicL2 d) :
    periodicIsWeakSolution d L mass hmass g (periodicMassiveResolvent d L mass hmass g) := by
  rw [periodicIsWeakSolution_iff]
  exact ⟨_, rfl, (periodicMassiveEmbedding d L mass hmass).solveIn_weak
    (periodicFourierHilbertBasis d) g⟩

/-- The sharp massive L2 estimate follows from the weak equation and energy
positivity, independently of the spectral multiplier representation. -/
theorem periodicMassiveResolvent_norm_le (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (g : PeriodicL2 d) :
    ‖periodicMassiveResolvent d L mass hmass g‖ ≤ (mass ^ 2)⁻¹ * ‖g‖ := by
  let A := periodicMassiveEmbedding d L mass hmass
  let b := periodicFourierHilbertBasis d
  let h := A.solveIn b g
  let u := periodicH1Value d L mass hmass h
  have hweak : ‖h‖ ^ 2 = (⟪g, u⟫_ℂ).re := by
    have hh := congrArg Complex.re (A.solveIn_weak b g h)
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, h, u,
      periodicH1Value] using hh
  have hcauchy : ‖h‖ ^ 2 ≤ ‖g‖ * ‖u‖ :=
    hweak.le.trans ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
  have hmassive : mass ^ 2 * ‖u‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [periodicH1_norm_sq_split d L mass hmass h]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  change ‖u‖ ≤ (mass ^ 2)⁻¹ * ‖g‖
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ (sq_pos_of_pos hmass)).mpr
  by_cases hu : ‖u‖ = 0
  · simp [hu]
  · have hupos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
    have hprod : (mass ^ 2 * ‖u‖ - ‖g‖) * ‖u‖ ≤ 0 := by
      nlinarith only [hcauchy, hmassive]
    have hcancel : mass ^ 2 * ‖u‖ - ‖g‖ ≤ 0 := by
      by_contra hn
      exact (not_lt_of_ge hprod) (mul_pos (lt_of_not_ge hn) hupos)
    nlinarith only [hcancel]

end Pphi2Clean.Continuum
