import Mathlib
noncomputable section
namespace OS1
open BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
def reflectedKernel (w : κ → ℝ) (a : κ → ι → ℝ) (i j : ι) : ℝ := ∑ p, w p * a p i * a p j
def quadratic (w : κ → ℝ) (a : κ → ι → ℝ) (c : ι → ℝ) : ℝ := ∑ i, ∑ j, c i * reflectedKernel w a i j * c j
 theorem test (w : κ → ℝ) (a : κ → ι → ℝ) (c : ι → ℝ) : quadratic w a c = ∑ p, w p * (∑ i, c i * a p i) ^ 2 := by
  classical
  simp only [quadratic, reflectedKernel, pow_two]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type]
  ring_nf
  simp only [← Fintype.sum_prod_type]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm]
end OS1
