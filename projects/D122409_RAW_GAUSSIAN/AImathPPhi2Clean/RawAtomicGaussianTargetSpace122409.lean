import AImathPPhi2Clean.RawAtomicGaussianTargetTail122409
import AImathPPhi2Clean.RawAtomicGaussianAtomicIdentity122409
import AImathPPhi2Clean.RawLiftDimension122409
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Bases
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false
noncomputable section
namespace Pphi2Clean.Dim122409Gaussian
open MeasureTheory Pphi2Clean.Continuum Pphi2Clean.UpstreamLattice
abbrev TargetCompletion := lp (fun _ : Index => ℂ) 2
instance : MeasurableSpace TargetCompletion := borel TargetCompletion
instance : BorelSpace TargetCompletion := ⟨rfl⟩
def targetCarrier (c : Index → ℂ) : Prop :=
  Summable (fun k => targetWeight k * ‖c k‖ ^ 2)
def targetWeightedCoefficients (c : Index → ℂ) : Index → ℂ :=
  fun k => (Real.sqrt (targetWeight k) : ℂ) * c k
theorem targetWeight_nonneg (k : Index) : 0 ≤ targetWeight k := by
  unfold targetWeight
  have hb : 0 ≤ 1 + ‖k‖ := by linarith [norm_nonneg k]
  exact Real.rpow_nonneg hb _
theorem targetWeightedCoefficients_memLp2 (c : Index → ℂ)
    (hc : targetCarrier c) : Memℓp (targetWeightedCoefficients c) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  change Summable (fun k => ‖(Real.sqrt (targetWeight k) : ℂ) * c k‖ ^ (2 : ℝ))
  change Summable (fun k => targetWeight k * ‖c k‖ ^ 2) at hc
  apply hc.congr
  intro k
  have hw := targetWeight_nonneg k
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt hw]
def targetEmbedding (c : Index → ℂ) (hc : targetCarrier c) : TargetCompletion :=
  ⟨targetWeightedCoefficients c, targetWeightedCoefficients_memLp2 c hc⟩
def targetSiteSequence (N : ℕ) [NeZero N] (a L : ℝ)
    (x : Pphi2Clean.Dim122409RawLift.Torus N) : Index → ℂ :=
  fun k => Pphi2Clean.Dim122409RawLift.siteCoefficient N a L x k
theorem rawSiteCoefficient_norm_sq (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (x : Pphi2Clean.Dim122409RawLift.Torus N) (k : Index) :
    ‖Pphi2Clean.Dim122409RawLift.siteCoefficient N a L x k‖ ^ 2 = a ^ (2 * 122409) := by
  rw [Pphi2Clean.Dim122409RawLift.siteCoefficient_norm N a L (le_of_lt ha) x k]
  rw [show (a ^ 122409) ^ 2 = a ^ (2 * 122409) by rw [← pow_mul]]
theorem targetSiteSequence_carrier (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (x : Pphi2Clean.Dim122409RawLift.Torus N) :
    targetCarrier (targetSiteSequence N a L x) := by
  have hweight : Summable targetWeight := by
    unfold targetWeight
    exact Pphi2Clean.DimensionFreeProbe.target_weight_summable
  have hmajor : Summable (fun k : Index => targetWeight k * a ^ (2 * 122409)) :=
    hweight.mul_right _
  apply hmajor.of_nonneg_of_le
  · intro k
    exact mul_nonneg (targetWeight_nonneg k) (sq_nonneg _)
  · intro k
    rw [targetSiteSequence, rawSiteCoefficient_norm_sq N a L ha x k]
def targetSiteVector (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a)
    (j : Fin (Fintype.card (FinLatticeSites 122409 N))) : TargetCompletion :=
  let x := (Fintype.equivFin (FinLatticeSites 122409 N)).symm j
  targetEmbedding (targetSiteSequence N a L x)
    (targetSiteSequence_carrier N a L ha x)
def targetCoefficientMap (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a)
    (c : Fin (Fintype.card (FinLatticeSites 122409 N)) → ℝ) : TargetCompletion :=
  ∑ j : Fin (Fintype.card (FinLatticeSites 122409 N)),
    c j • targetSiteVector N a L ha j
theorem continuous_targetCoefficientMap (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) : Continuous (targetCoefficientMap N a L ha) := by
  unfold targetCoefficientMap
  apply continuous_finsetSum
  intro j hj
  exact (continuous_apply j).smul continuous_const
def actualTargetLift (N : ℕ) [NeZero N] (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ξ : FiniteConfig N) : TargetCompletion :=
  targetCoefficientMap N a L ha
    (fun j => ξ (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 122409 N))))
theorem continuous_actualTargetLift (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    Continuous (actualTargetLift N a L ha hL) := by
  unfold actualTargetLift targetCoefficientMap
  apply continuous_finsetSum
  intro j hj
  exact (WeakDual.eval_continuous (Pi.single j (1 : ℝ) : FiniteLatticeField
    (Fintype.card (FinLatticeSites 122409 N)))).smul continuous_const
theorem actualTargetLift_apply (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L) (ξ : FiniteConfig N) (k : Index) :
    actualTargetLift N a L ha hL ξ k =
      (Real.sqrt (targetWeight k) : ℂ) * actualRawAtomicLift N a L hL ξ k := by
  unfold actualTargetLift targetCoefficientMap
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    targetSiteVector, targetEmbedding, targetWeightedCoefficients,
    targetSiteSequence, Complex.real_smul]
  rw [actualRawAtomicLift_eq_rawAtomicFourierLift N a L hL ξ k]
  let e := Fintype.equivFin (Pphi2Clean.Dim122409RawLift.Torus N)
  have hreindex :
      (∑ j : Fin (Fintype.card (Pphi2Clean.Dim122409RawLift.Torus N)),
        (ξ (Pi.single j (1 : ℝ)) : ℂ) *
          Pphi2Clean.Dim122409RawLift.siteCoefficient N a L (e.symm j) k) =
      ∑ x : Pphi2Clean.Dim122409RawLift.Torus N,
        (ξ (Pi.single (e x) (1 : ℝ)) : ℂ) *
          Pphi2Clean.Dim122409RawLift.siteCoefficient N a L x k := by
    simpa [e] using (e.symm.sum_comp (fun x : Pphi2Clean.Dim122409RawLift.Torus N =>
      (ξ (Pi.single (e x) (1 : ℝ)) : ℂ) *
        Pphi2Clean.Dim122409RawLift.siteCoefficient N a L x k))
  unfold Pphi2Clean.Dim122409RawLift.rawAtomicFourierLift rawLiftSourceField122409
  calc
    _ = (Real.sqrt (targetWeight k) : ℂ) *
        ∑ j : Fin (Fintype.card (Pphi2Clean.Dim122409RawLift.Torus N)),
          (ξ (Pi.single j (1 : ℝ)) : ℂ) *
            Pphi2Clean.Dim122409RawLift.siteCoefficient N a L (e.symm j) k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [e, mul_comm]
      ring
    _ = (Real.sqrt (targetWeight k) : ℂ) *
        ∑ x : Pphi2Clean.Dim122409RawLift.Torus N,
          (ξ (Pi.single (e x) (1 : ℝ)) : ℂ) *
            Pphi2Clean.Dim122409RawLift.siteCoefficient N a L x k := by rw [hreindex]
#print axioms actualTargetLift_apply
#print axioms continuous_actualTargetLift
end Pphi2Clean.Dim122409Gaussian
