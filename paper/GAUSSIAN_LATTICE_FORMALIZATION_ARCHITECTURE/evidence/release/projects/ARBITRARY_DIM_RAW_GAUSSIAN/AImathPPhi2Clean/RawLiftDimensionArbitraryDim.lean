import AImathPPhi2Clean.ArbitraryDimParameters
import AImathPPhi2Clean.DimensionFreeWeightSummability
import Mathlib
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace Pphi2Clean.ArbitraryDimRawLift
open Pphi2Clean.ArbitraryDim
variable [Parameters]

abbrev Index := Fin dimension → ℤ
abbrev Torus (N : ℕ) := Fin dimension → ZMod N

def energyWeight (k : Index) : ℝ := (1 + ‖k‖) ^ (-2 * energyOrder)
def sitePhase (N : ℕ) [NeZero N] (a L : ℝ) (x : Torus N) (k : Index) : ℝ :=
  (2 * Real.pi / L) * ∑ i : Fin dimension, (k i : ℝ) * (a * ((x i).val : ℝ))
def siteCoefficient (N : ℕ) [NeZero N] (a L : ℝ) (x : Torus N) (k : Index) : ℂ :=
  (a ^ dimension : ℂ) * Complex.exp ((sitePhase N a L x k : ℂ) * Complex.I)
def rawAtomicFourierLift (N : ℕ) [NeZero N] (a L : ℝ)
    (field : Torus N → ℝ) (k : Index) : ℂ :=
  ∑ x : Torus N, (field x : ℂ) * siteCoefficient N a L x k
def energyCarrier (c : Index → ℂ) : Prop := Summable (fun k => energyWeight k * ‖c k‖ ^ 2)
def finiteFieldBound (N : ℕ) [NeZero N] (a : ℝ) (field : Torus N → ℝ) : ℝ :=
  ∑ x : Torus N, ‖(field x : ℂ)‖ * a ^ dimension

lemma energyWeight_nonneg (k : Index) : 0 ≤ energyWeight k := by
  unfold energyWeight
  have hbase : 0 ≤ 1 + ‖k‖ := by positivity
  exact Real.rpow_nonneg hbase _

theorem siteCoefficient_norm (N : ℕ) [NeZero N] (a L : ℝ)
    (ha : 0 ≤ a) (x : Torus N) (k : Index) :
    ‖siteCoefficient N a L x k‖ = a ^ dimension := by
  rw [siteCoefficient, ← Complex.ofReal_pow, Complex.norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha _),
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem rawAtomicFourierLift_norm_le (N : ℕ) [NeZero N] (a L : ℝ)
    (ha : 0 ≤ a) (field : Torus N → ℝ) (k : Index) :
    ‖rawAtomicFourierLift N a L field k‖ ≤ finiteFieldBound N a field := by
  unfold rawAtomicFourierLift finiteFieldBound
  calc
    ‖∑ x : Torus N, (field x : ℂ) * siteCoefficient N a L x k‖ ≤
        ∑ x : Torus N, ‖(field x : ℂ) * siteCoefficient N a L x k‖ := norm_sum_le _ _
    _ = ∑ x : Torus N, ‖(field x : ℂ)‖ * a ^ dimension := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Complex.norm_mul, siteCoefficient_norm N a L ha x k]

theorem finiteFieldBound_nonneg (N : ℕ) [NeZero N] (a : ℝ)
    (ha : 0 ≤ a) (field : Torus N → ℝ) : 0 ≤ finiteFieldBound N a field := by
  unfold finiteFieldBound
  exact Finset.sum_nonneg fun x hx => mul_nonneg (norm_nonneg _) (pow_nonneg ha _)

theorem rawAtomicFourierLift_mem_energyCarrier (N : ℕ) [NeZero N]
    (a L : ℝ) (ha : 0 ≤ a) (field : Torus N → ℝ) :
    energyCarrier (rawAtomicFourierLift N a L field) := by
  let B := finiteFieldBound N a field
  have hmajor : Summable (fun k : Index => energyWeight k * B ^ 2) := by
    have h := Pphi2Clean.ArbitraryDim.energy_weight_summable.mul_right (B ^ 2)
    simpa [energyWeight] using h
  have hB : 0 ≤ B := finiteFieldBound_nonneg N a ha field
  unfold energyCarrier
  apply hmajor.of_nonneg_of_le
  · intro k
    exact mul_nonneg (energyWeight_nonneg k) (sq_nonneg _)
  · intro k
    have hb := rawAtomicFourierLift_norm_le N a L ha field k
    change ‖rawAtomicFourierLift N a L field k‖ ≤ B at hb
    apply mul_le_mul_of_nonneg_left _ (energyWeight_nonneg k)
    exact (sq_le_sq₀ (norm_nonneg _) hB).2 hb

theorem rawAtomicFourierLift_eq_sum (N : ℕ) [NeZero N] (a L : ℝ)
    (field : Torus N → ℝ) (k : Index) :
    rawAtomicFourierLift N a L field k =
      ∑ x : Torus N, (field x : ℂ) * siteCoefficient N a L x k := rfl

#print axioms siteCoefficient_norm
#print axioms rawAtomicFourierLift_mem_energyCarrier
end Pphi2Clean.ArbitraryDimRawLift
