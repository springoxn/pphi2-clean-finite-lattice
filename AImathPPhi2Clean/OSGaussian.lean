import AImathPPhi2Clean.OSPositivity

noncomputable section

namespace Pphi2Clean.OS

/-- A finite-dimensional Gaussian kernel on a finite state space. -/
def gaussianKernel (σ : ℝ) (x y : Fin n) : ℝ :=
  Real.exp (-((((x : ℝ) - (y : ℝ)) ^ 2) / (2 * σ ^ 2)))

theorem gaussianKernel_pos (σ : ℝ) (x y : Fin n) :
    0 < gaussianKernel σ x y := by
  unfold gaussianKernel
  exact Real.exp_pos _

/-- The finite-dimensional Gaussian transfer is positivity improving for every
positive width. The proof uses pointwise positivity only, with no uniform lower
bound in the states. -/
theorem gaussian_transfer_isPositivityImproving
    (n : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    IsPositivityImproving n (gaussianKernel (n := n) σ) := by
  exact transfer_isPositivityImproving n (gaussianKernel (n := n) σ)
    (fun x y => gaussianKernel_pos σ x y)

end Pphi2Clean.OS
