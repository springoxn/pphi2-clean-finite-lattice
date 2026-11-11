import AImathPPhi2Clean.Periodic3DCarrierEnergy

noncomputable section
namespace Pphi2Clean.Continuum

open Pphi2Clean.UpstreamLattice

theorem periodic3DRawAtomicLift_mem_carrier_two (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (ω : FiniteLatticeConfiguration (Fintype.card (FinLatticeSites 3 N))) :
    periodic3DRawAtomicLift N a L hL ω ∈ periodic3DCarrier 2 := by
  have hcos (k : Periodic3DIndex) :
      (latticeEmbedLift (physicalTestEval 3 N a) ω) (periodicCosineTest 3 L k hL) =
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
      (latticeEmbedLift (physicalTestEval 3 N a) ω) (periodicSineTest 3 L k hL) =
        ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ω (Pi.single j (1 : ℝ) : FiniteLatticeField
            (Fintype.card (FinLatticeSites 3 N))) *
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) := by
    rw [latticeEmbedLift_eval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalTestEval_periodicSineTest_apply 3 N a L ha k hL j]
    rfl
  have hseq : periodic3DRawAtomicLift N a L hL ω =
      fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
          (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
          periodic3DSiteSequence N a L j k := by
    funext k
    simp only [periodic3DRawAtomicLift, periodic3DComplexFourierLift]
    rw [hcos k, hsin k]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_cos,
      Complex.ofReal_sin, periodic3DSiteSequence]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hseq, periodic3DCarrier]
  let c : Fin (Fintype.card (FinLatticeSites 3 N)) → ℝ := fun j =>
    ω (Pi.single j (1 : ℝ) : FiniteLatticeField
      (Fintype.card (FinLatticeSites 3 N)))
  let B : ℝ := ∑ j, |c j| * a ^ 3
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (abs_nonneg _) (by positivity))
  have hmode (j : Fin (Fintype.card (FinLatticeSites 3 N))) (k : Periodic3DIndex) :
      ‖periodic3DSiteSequence N a L j k‖ = a ^ 3 := by
    have hsq : ‖periodic3DSiteSequence N a L j k‖ ^ 2 = a ^ 6 := by
      dsimp [periodic3DSiteSequence]
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      calc
        (a ^ 3 * Real.cos (periodic3DSitePhase N a L j k)) ^ 2 +
            (a ^ 3 * Real.sin (periodic3DSitePhase N a L j k)) ^ 2 =
            a ^ 6 * (Real.cos (periodic3DSitePhase N a L j k) ^ 2 +
              Real.sin (periodic3DSitePhase N a L j k) ^ 2) := by ring
        _ = a ^ 6 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    have hn := norm_nonneg (periodic3DSiteSequence N a L j k)
    have ha3 : 0 ≤ a ^ 3 := by positivity
    nlinarith
  have hbound (k : Periodic3DIndex) :
      ‖∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
        (c j : ℂ) * periodic3DSiteSequence N a L j k‖ ≤ B := by
    calc
      _ ≤ ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          ‖(c j : ℂ) * periodic3DSiteSequence N a L j k‖ := norm_sum_le _ _
      _ = B := by
        simp [B, hmode, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ a ^ 3)]
  have hw (k : Periodic3DIndex) : 0 ≤ periodic3DHminusTwoWeight k :=
    periodic3DSobolevWeight_nonneg 2 k
  have hmajor : Summable (fun k : Periodic3DIndex =>
      B ^ 2 * periodic3DHminusTwoWeight k) :=
    periodic3DHminusTwoWeight_summable.mul_left (B ^ 2)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (hw k) (sq_nonneg _))
    (fun k => by
      have hb' : ‖∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
          (c j : ℂ) * periodic3DSiteSequence N a L j k‖ ≤ B := hbound k
      calc
        periodic3DHminusTwoWeight k *
            ‖(fun k => ∑ j : Fin (Fintype.card (FinLatticeSites 3 N)),
              (ω (Pi.single j (1 : ℝ) : FiniteLatticeField
                (Fintype.card (FinLatticeSites 3 N))) : ℂ) *
              periodic3DSiteSequence N a L j k) k‖ ^ 2 ≤
            periodic3DHminusTwoWeight k * B ^ 2 :=
          mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hB).2 (by simpa [c] using hb')) (hw k)
        _ = B ^ 2 * periodic3DHminusTwoWeight k := by ring) hmajor

end Pphi2Clean.Continuum
