import AImathPPhi2Clean.Periodic3DFiniteSourceLift
import AImathPPhi2Clean.Periodic3DWeightedCarrier
import AImathPPhi2Clean.RealFourierTestFunctions

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Pphi2Clean.UpstreamLattice

instance : MeasurableSpace Periodic3DCompletion := borel Periodic3DCompletion
instance : BorelSpace Periodic3DCompletion := ⟨rfl⟩

def periodic3DSiteWeightedSequence (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) : Periodic3DIndex → ℂ :=
  fun k => (Real.sqrt (periodic3DHminusFourWeight k) : ℂ) *
    periodic3DSiteSequence N a L j k

theorem periodic3DSiteWeightedSequence_memLp (N : ℕ) [NeZero N]
    (a L : ℝ) (j : Fin (Fintype.card (FinLatticeSites 3 N))) :
    Memℓp (periodic3DSiteWeightedSequence N a L j) 2 := by
  exact periodic3D_weighted_coefficients_memLp2 4
    (periodic3DSiteSequence N a L j)
    (periodic3DSiteSequence_mem_carrier N a L j)

def periodic3DSiteVector (N : ℕ) [NeZero N] (a L : ℝ)
    (j : Fin (Fintype.card (FinLatticeSites 3 N))) : Periodic3DCompletion :=
  ⟨periodic3DSiteWeightedSequence N a L j,
    periodic3DSiteWeightedSequence_memLp N a L j⟩

def periodic3DFiniteSourceCoefficientMap (N : ℕ) [NeZero N]
    (a L : ℝ) (c : Fin (Fintype.card (FinLatticeSites 3 N)) → ℝ) :
    Periodic3DCompletion :=
  ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
    c j • periodic3DSiteVector N a L j

theorem continuous_periodic3DFiniteSourceCoefficientMap (N : ℕ) [NeZero N]
    (a L : ℝ) : Continuous (periodic3DFiniteSourceCoefficientMap N a L) := by
  unfold periodic3DFiniteSourceCoefficientMap
  exact continuous_finsetSum Finset.univ (fun j _ =>
    (continuous_apply j).smul continuous_const)

def periodic3DFiniteSourceFourierLift (N : ℕ) [NeZero N]
    (a L : ℝ)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    Periodic3DCompletion :=
  periodic3DFiniteSourceCoefficientMap N a L
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N))) )

theorem measurable_periodic3DFiniteSourceFourierLift (N : ℕ) [NeZero N]
    (a L : ℝ) : Measurable (periodic3DFiniteSourceFourierLift N a L) := by
  unfold periodic3DFiniteSourceFourierLift
  have hcoords : Measurable (fun ω : FiniteLatticeConfiguration
      (Fintype.card (FinLatticeSites 3 N)) =>
        fun j : Fin (Fintype.card (FinLatticeSites 3 N)) =>
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N)))) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N)))).comp (comap_measurable _)
  exact (continuous_periodic3DFiniteSourceCoefficientMap N a L).measurable.comp hcoords

theorem periodic3DFiniteSourceFourierLift_apply (N : ℕ) [NeZero N]
    (a L : ℝ)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N)))
    (k : Periodic3DIndex) :
    periodic3DFiniteSourceFourierLift N a L ω k =
      ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
          periodic3DSiteWeightedSequence N a L j k := by
  change (⇑(periodic3DFiniteSourceCoefficientMap N a L
    (fun j => ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N)))))) k = _
  rw [periodic3DFiniteSourceCoefficientMap, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    periodic3DSiteVector, Complex.real_smul]

theorem periodic3DRawAtomicLift_eq_site_sum (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DRawAtomicLift N a L hL ω =
      fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
          periodic3DSiteSequence N a L j k := by
  have hcos (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω)
          (periodicCosineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.cos (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicCosineTest_apply 3 N a L ha k hL j]
    rfl
  have hsin (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω)
          (periodicSineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 3 N a L ha k hL j]
    rfl
  funext k
  simp only [periodic3DRawAtomicLift, periodic3DComplexFourierLift]
  rw [hcos k, hsin k]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
    Complex.ofReal_sin, periodic3DSiteSequence]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem periodic3DRawWeightedLift_eq_finiteSourceFourierLift (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    (fun k => (Real.sqrt (periodic3DHminusFourWeight k) : ℂ) *
        periodic3DRawAtomicLift N a L hL ω k) =
      fun k => periodic3DFiniteSourceFourierLift N a L ω k := by
  funext k
  rw [periodic3DRawAtomicLift_eq_site_sum N a L ha hL ω]
  rw [periodic3DFiniteSourceFourierLift_apply]
  simp only [periodic3DSiteWeightedSequence]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Pphi2Clean.Continuum
