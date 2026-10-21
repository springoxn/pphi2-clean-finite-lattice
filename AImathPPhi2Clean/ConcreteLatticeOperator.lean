/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.

Finite-lattice definitions and proofs adapted from mrdouglasny/GaussianField,
commit d63a28568a75d99f6cb27af1f888a49a69855a66,
Lattice/FiniteField.lean, Lattice/Laplacian.lean, Lattice/SpectralCovariance.lean.
The migration excludes infinite-lattice and continuum-limit declarations.
-/
import AImathPPhi2Clean.RealLatticeSpectralCovariance
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Basic
noncomputable section
namespace Pphi2Clean.UpstreamLattice
/-! ## Site types -/

/-- Finite lattice sites: the discrete torus (ℤ/Nℤ)^d with periodic BC. -/
abbrev FinLatticeSites (d : ℕ) (N : ℕ) := Fin d → ZMod N

/-- Infinite lattice sites: ℤ^d. -/
abbrev InfLatticeSites (d : ℕ) := Fin d → ℤ


abbrev FinLatticeField (d N : ℕ) := FinLatticeSites d N → ℝ

def finLatticeDelta {d N : ℕ} (x : FinLatticeSites d N) : FinLatticeField d N :=
  fun y => if y = x then 1 else 0

/-! ## Finite Laplacian -/

/-- The discrete Laplacian on the finite torus (ℤ/Nℤ)^d with spacing `a`.

`(Δ_a f)(x) = (1/a²) Σᵢ [f(x + eᵢ) + f(x - eᵢ) - 2f(x)]`

where addition is modulo N (periodic boundary conditions). -/
def finiteLaplacianFun (d N : ℕ) [NeZero N] (a : ℝ) (f : FinLatticeField d N)
    (x : FinLatticeSites d N) : ℝ :=
  a⁻¹ ^ 2 * ∑ i : Fin d,
    (f (fun j => if j = i then x j + 1 else x j) +
     f (fun j => if j = i then x j - 1 else x j) -
     2 * f x)

/-- The finite Laplacian as a continuous linear map. Continuity is automatic
since FinLatticeField d N is finite-dimensional. -/
def finiteLaplacianLM (d N : ℕ) [NeZero N] (a : ℝ) :
    FinLatticeField d N →ₗ[ℝ] FinLatticeField d N where
  toFun := finiteLaplacianFun d N a
  map_add' := fun f g => by
    funext x; simp only [finiteLaplacianFun, Pi.add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  map_smul' := fun r f => by
    funext x; simp only [finiteLaplacianFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    -- Factor r out of each summand, then pull through sum and a⁻¹²
    have : ∀ i : Fin d,
        (r * (f fun j => if j = i then x j + 1 else x j)) +
        (r * (f fun j => if j = i then x j - 1 else x j)) -
        2 * (r * f x) =
        r * (((f fun j => if j = i then x j + 1 else x j) +
              (f fun j => if j = i then x j - 1 else x j)) -
             2 * f x) := fun i => by ring
    simp_rw [this, ← Finset.mul_sum, ← mul_assoc, mul_comm (a⁻¹ ^ 2) r]

/-- The finite Laplacian as a continuous linear map. Continuity is automatic
since FinLatticeField d N is finite-dimensional. -/
noncomputable def finiteLaplacian (d N : ℕ) [NeZero N] (a : ℝ) :
    FinLatticeField d N →L[ℝ] FinLatticeField d N :=
  { finiteLaplacianLM d N a with
    cont := (finiteLaplacianLM d N a).continuous_of_finiteDimensional }

/-! ## Properties of the finite Laplacian -/

/-- The finite Laplacian is self-adjoint (symmetric matrix).
Proof: exchange of summation indices using periodicity. -/
private lemma update_add_eq {d N : ℕ} [NeZero N] (x : FinLatticeSites d N)
    (i : Fin d) (c : ZMod N) :
    (fun j => if j = i then x j + c else x j) = x + Pi.single i c := by
  ext j; simp only [Pi.add_apply, Pi.single_apply]
  split_ifs with h <;> simp [h]

private lemma update_sub_eq {d N : ℕ} [NeZero N] (x : FinLatticeSites d N)
    (i : Fin d) (c : ZMod N) :
    (fun j => if j = i then x j - c else x j) = x - Pi.single i c := by
  ext j; simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs with h <;> simp [h]

private lemma sum_mul_shift_fwd {d N : ℕ} [NeZero N]
    (h k : FinLatticeField d N) (v : FinLatticeSites d N) :
    ∑ x, h x * k (x + v) = ∑ x, h (x - v) * k x := by
  symm; exact Fintype.sum_equiv (Equiv.addRight (-v))
    (fun x => h (x - v) * k x) (fun x => h x * k (x + v))
    (fun x => by simp [sub_eq_add_neg])

private lemma sum_mul_shift_bwd {d N : ℕ} [NeZero N]
    (h k : FinLatticeField d N) (v : FinLatticeSites d N) :
    ∑ x, h x * k (x - v) = ∑ x, h (x + v) * k x := by
  symm; exact Fintype.sum_equiv (Equiv.addRight v)
    (fun x => h (x + v) * k x) (fun x => h x * k (x - v))
    (fun x => by simp [add_sub_cancel_right])

/-- Helper: The Laplacian inner product for a single direction, after expanding. -/
private lemma laplacian_direction_eq {d N : ℕ} [NeZero N]
    (f g : FinLatticeField d N) (i : Fin d) (a : ℝ) :
    ∑ x, f x * (a⁻¹ ^ 2 * ((g (x + Pi.single i (1 : ZMod N)) +
      g (x - Pi.single i (1 : ZMod N))) - 2 * g x)) =
    ∑ x, a⁻¹ ^ 2 * ((f (x + Pi.single i (1 : ZMod N)) +
      f (x - Pi.single i (1 : ZMod N))) - 2 * f x) * g x := by
  -- Expand both sides into three terms
  have lhs_expand : ∀ x : FinLatticeSites d N,
      f x * (a⁻¹ ^ 2 * ((g (x + Pi.single i (1 : ZMod N)) +
        g (x - Pi.single i (1 : ZMod N))) - 2 * g x)) =
      a⁻¹ ^ 2 * (f x * g (x + Pi.single i 1)) +
      a⁻¹ ^ 2 * (f x * g (x - Pi.single i 1)) +
      a⁻¹ ^ 2 * (-(2 : ℝ) * (f x * g x)) := by intro; ring
  have rhs_expand : ∀ x : FinLatticeSites d N,
      a⁻¹ ^ 2 * ((f (x + Pi.single i (1 : ZMod N)) +
        f (x - Pi.single i (1 : ZMod N))) - 2 * f x) * g x =
      a⁻¹ ^ 2 * (f (x + Pi.single i 1) * g x) +
      a⁻¹ ^ 2 * (f (x - Pi.single i 1) * g x) +
      a⁻¹ ^ 2 * (-(2 : ℝ) * (f x * g x)) := by intro; ring
  simp_rw [lhs_expand, rhs_expand, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Diagonal terms match. Reindex the shift terms.
  have h1 : ∑ x, f x * g (x + Pi.single i (1 : ZMod N)) =
      ∑ x, f (x - Pi.single i (1 : ZMod N)) * g x :=
    sum_mul_shift_fwd f g _
  have h2 : ∑ x, f x * g (x - Pi.single i (1 : ZMod N)) =
      ∑ x, f (x + Pi.single i (1 : ZMod N)) * g x :=
    sum_mul_shift_bwd f g _
  rw [h1, h2]; ring

/-- The finite Laplacian is self-adjoint: ⟨f, Δg⟩ = ⟨Δf, g⟩. -/
theorem finiteLaplacian_selfAdjoint (d N : ℕ) [NeZero N] (a : ℝ)
    (f g : FinLatticeField d N) :
    ∑ x, f x * (finiteLaplacian d N a g) x =
    ∑ x, (finiteLaplacian d N a f) x * g x := by
  -- Unfold to the raw function definition
  change ∑ x, f x * finiteLaplacianFun d N a g x =
    ∑ x, finiteLaplacianFun d N a f x * g x
  simp only [finiteLaplacianFun]
  simp_rw [update_add_eq, update_sub_eq]
  -- Pull the direction sum outside and swap with the site sum
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_rhs => rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  congr 1; ext i
  exact laplacian_direction_eq f g i a

/-- For each lattice direction, the inner product ∑ₓ f(x)·Δᵢf(x) equals
minus a sum of squares: -(∑ₓ (f(x+eᵢ) - f(x))²). -/
private lemma direction_sum_eq_neg_sq {d N : ℕ} [NeZero N]
    (f : FinLatticeField d N) (i : Fin d) :
    ∑ x : FinLatticeSites d N,
      f x * (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x) =
    -(∑ x : FinLatticeSites d N, (f (x + Pi.single i 1) - f x) ^ 2) := by
  have reindex_sq : ∑ x : FinLatticeSites d N, f (x + Pi.single i 1) ^ 2 =
      ∑ x : FinLatticeSites d N, f x ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : ZMod N)))
      (fun x => f (x + Pi.single i 1) ^ 2) (fun x => f x ^ 2)
      (fun x => by simp)
  have shift_bwd : ∑ x : FinLatticeSites d N, f x * f (x - Pi.single i 1) =
      ∑ x : FinLatticeSites d N, f (x + Pi.single i 1) * f x :=
    sum_mul_shift_bwd f f _
  have comm_sum : ∑ x : FinLatticeSites d N, f (x + Pi.single i 1) * f x =
      ∑ x : FinLatticeSites d N, f x * f (x + Pi.single i 1) :=
    Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have lhs_eq : ∑ x : FinLatticeSites d N,
      f x * (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x) =
      (∑ x : FinLatticeSites d N, f x * f (x + Pi.single i 1)) +
      (∑ x : FinLatticeSites d N, f x * f (x - Pi.single i 1)) +
      (-2) * (∑ x : FinLatticeSites d N, f x ^ 2) := by
    have h1 : ∀ x : FinLatticeSites d N,
        f x * (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x) =
        f x * f (x + Pi.single i 1) + f x * f (x - Pi.single i 1) +
        (-2) * (f x ^ 2) := by intro; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [lhs_eq, shift_bwd, comm_sum]
  have rhs_eq : -(∑ x : FinLatticeSites d N, (f (x + Pi.single i 1) - f x) ^ 2) =
      -(∑ x : FinLatticeSites d N, f (x + Pi.single i 1) ^ 2) +
      2 * (∑ x : FinLatticeSites d N, f x * f (x + Pi.single i 1)) +
      (-1) * (∑ x : FinLatticeSites d N, f x ^ 2) := by
    have h2 : ∀ x : FinLatticeSites d N,
        (f (x + Pi.single i 1) - f x) ^ 2 =
        f (x + Pi.single i 1) ^ 2 + (-2) * (f x * f (x + Pi.single i 1)) +
        f x ^ 2 := by intro; ring
    simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [rhs_eq, reindex_sq]
  ring

/-- The finite Laplacian is negative semidefinite: ⟨f, Δf⟩ ≤ 0.
Proof: summation by parts gives -a⁻² Σᵢ Σₓ (f(x+eᵢ) - f(x))² ≤ 0. -/
theorem finiteLaplacian_neg_semidefinite (d N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (f : FinLatticeField d N) :
    ∑ x, f x * (finiteLaplacian d N a f) x ≤ 0 := by
  let _ha := ha
  change ∑ x, f x * finiteLaplacianFun d N a f x ≤ 0
  simp only [finiteLaplacianFun]
  simp_rw [update_add_eq, update_sub_eq]
  -- Rewrite to a⁻¹² * ∑_i ∑_x f(x)·(D_i f)(x) and swap sums
  have step1 : (∑ x : FinLatticeSites d N,
      f x * (a⁻¹ ^ 2 * ∑ i : Fin d,
        (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x))) =
    a⁻¹ ^ 2 * ∑ i : Fin d, ∑ x : FinLatticeSites d N,
      (f x * (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x)) := by
    conv_lhs =>
      arg 2; ext x
      rw [mul_comm (f x) (a⁻¹ ^ 2 * _), mul_assoc, Finset.sum_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1; apply Finset.sum_congr rfl
    intro i _; apply Finset.sum_congr rfl
    intro x _; ring
  rw [step1]
  simp_rw [direction_sum_eq_neg_sq]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact sq_nonneg _
  · exact Finset.sum_nonpos (fun i _ =>
      neg_nonpos_of_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)))

/-! ## Mass operator -/

/-- The mass operator `-Δ_a + m²` on the finite lattice.
This is the covariance operator's inverse in the lattice Gaussian measure. -/
def massOperator (d N : ℕ) [NeZero N] (a mass : ℝ) :
    FinLatticeField d N →L[ℝ] FinLatticeField d N :=
  -finiteLaplacian d N a + mass ^ 2 • ContinuousLinearMap.id ℝ _

/-- The mass operator is positive definite when mass > 0.
Proof: ⟨f, (-Δ+m²)f⟩ = -⟨f,Δf⟩ + m²‖f‖² ≥ m²‖f‖² > 0 for f ≠ 0. -/
theorem massOperator_pos_def (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (hf : f ≠ 0) :
    0 < ∑ x, f x * (massOperator d N a mass f) x := by
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  have split : ∀ x : FinLatticeSites d N,
      f x * (-(finiteLaplacian d N a f) x + mass ^ 2 * f x) =
      -(f x * (finiteLaplacian d N a f) x) + mass ^ 2 * f x ^ 2 := by
    intro x; ring
  simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
  have h_neg : 0 ≤ -(∑ x : FinLatticeSites d N, f x * (finiteLaplacian d N a f) x) :=
    neg_nonneg.mpr (finiteLaplacian_neg_semidefinite d N a ha f)
  have h_sq_pos : 0 < ∑ x : FinLatticeSites d N, f x ^ 2 := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h; push Not at h; exact hf (funext h)
    exact Finset.sum_pos' (fun x _ => sq_nonneg (f x)) ⟨x, Finset.mem_univ _, by positivity⟩
  linarith [mul_pos (sq_pos_of_pos hmass) h_sq_pos]


variable (d N : ℕ) [NeZero N]

/-! ## Mass operator as a matrix -/

/-- The "matrix entries" of the mass operator: the bilinear form evaluated
on delta functions. `Q(x,y) = ⟨δ_x, (-Δ+m²)(δ_y)⟩ = (Q δ_y)(x)`. -/
def massOperatorEntry (a mass : ℝ)
    (x y : FinLatticeSites d N) : ℝ :=
  (massOperator d N a mass (finLatticeDelta y)) x

/-- The mass operator `Q = -Δ + m²` as a matrix indexed by lattice sites.
Entry `(x, y)` is `⟨δ_x, Q(δ_y)⟩ = (Q δ_y)(x)`. -/
def massOperatorMatrix (a mass : ℝ) :
    Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ :=
  fun x y => massOperatorEntry d N a mass x y

/-! ## Self-adjointness -/

/-- The mass operator is self-adjoint: `⟨f, Qg⟩ = ⟨Qf, g⟩`. -/
theorem massOperator_selfAdjoint (a mass : ℝ)
    (f g : FinLatticeField d N) :
    ∑ x, f x * (massOperator d N a mass g) x =
    ∑ x, (massOperator d N a mass f) x * g x := by
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  -- Split into Laplacian and mass terms
  have split_l : ∀ x, f x * (-(finiteLaplacian d N a g) x + mass ^ 2 * g x) =
      -(f x * (finiteLaplacian d N a g) x) + mass ^ 2 * (f x * g x) := by
    intro x; ring
  have split_r : ∀ x, (-(finiteLaplacian d N a f) x + mass ^ 2 * f x) * g x =
      -((finiteLaplacian d N a f) x * g x) + mass ^ 2 * (f x * g x) := by
    intro x; ring
  simp_rw [split_l, split_r, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  congr 1
  -- The Laplacian part follows from finiteLaplacian_selfAdjoint
  rw [finiteLaplacian_selfAdjoint d N a f g]

/-- The mass operator matrix is Hermitian (symmetric over ℝ).

Proof: Self-adjointness of Q applied to delta functions gives
`Q(x,y) = (Qδ_y)(x) = ⟨δ_x, Qδ_y⟩ = ⟨Qδ_x, δ_y⟩ = (Qδ_x)(y) = Q(y,x)`. -/
theorem massOperatorMatrix_isHermitian (a mass : ℝ) :
    (massOperatorMatrix d N a mass).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have h := massOperator_selfAdjoint d N a mass
    (finLatticeDelta j) (finLatticeDelta i)
  simpa [Matrix.conjTranspose, massOperatorMatrix, massOperatorEntry, finLatticeDelta] using h


/-! ## Eigenvectors and eigenvalues -/

abbrev massMatrixHerm (a mass : ℝ) :=
  massOperatorMatrix_isHermitian d N a mass

def massEigenvalues (a mass : ℝ) : FinLatticeSites d N → ℝ :=
  (massMatrixHerm d N a mass).eigenvalues

def massEigenvectorBasis (a mass : ℝ) :
    OrthonormalBasis (FinLatticeSites d N) ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) :=
  (massMatrixHerm d N a mass).eigenvectorBasis

section
set_option linter.unusedSectionVars false
/-- Basis decomposition: any lattice field is a linear combination of deltas. -/
private lemma field_basis_decomp (φ : FinLatticeField d N) :
    φ = ∑ y : FinLatticeSites d N, φ y • finLatticeDelta y := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finLatticeDelta,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
end

/-- The mass operator applied to f equals the matrix-vector product.

This bridges the CLM `massOperator` with the matrix `massOperatorMatrix`:
`(Q f)(x) = Σ_y Q(x,y) · f(y) = (M *ᵥ f)(x)`. -/
theorem massOperator_eq_matrix_mulVec (a mass : ℝ)
    (f : FinLatticeField d N) (x : FinLatticeSites d N) :
    (massOperator d N a mass f) x =
    (massOperatorMatrix d N a mass).mulVec f x := by
  -- (Q f)(x) = Σ_y Q(x,y) f(y) = (M *ᵥ f)(x) by linearity + basis expansion
  simp only [Matrix.mulVec, massOperatorMatrix]
  conv_lhs => rw [field_basis_decomp d N f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1; ext y
  -- f y * (Q δ_y)(x) = massOperatorEntry x y * f y
  unfold massOperatorEntry
  ring

/-- In eigenbasis coefficients, the mass operator acts by scalar multiplication
by the corresponding eigenvalue. -/
theorem massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff (a mass : ℝ)
    (f : FinLatticeField d N) (k : FinLatticeSites d N) :
    (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          (massOperator d N a mass f) x) =
      massEigenvalues d N a mass k *
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
  have hswap := massOperator_selfAdjoint d N a mass
    (massEigenvectorBasis d N a mass k) f
  have hright :
      ∑ x : FinLatticeSites d N,
          (massOperator d N a mass (massEigenvectorBasis d N a mass k)) x * f x =
        massEigenvalues d N a mass k *
          (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
    have hmul :
        massOperator d N a mass (massEigenvectorBasis d N a mass k) =
          massEigenvalues d N a mass k • (massEigenvectorBasis d N a mass k) := by
      ext x
      rw [massOperator_eq_matrix_mulVec (d := d) (N := N) a mass
        (massEigenvectorBasis d N a mass k) x]
      simpa [massEigenvalues, massEigenvectorBasis] using
        congrFun (Matrix.IsHermitian.mulVec_eigenvectorBasis
          (hA := massOperatorMatrix_isHermitian d N a mass) k) x
    rw [hmul]
    calc
      ∑ x : FinLatticeSites d N,
          (massEigenvalues d N a mass k *
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) * f x
          = ∑ x : FinLatticeSites d N,
              massEigenvalues d N a mass k *
                ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
            rw [Finset.mul_sum]
  rw [hright] at hswap
  exact hswap

/-- Parseval identity in the mass-operator eigenbasis, written in site
coordinates. -/
theorem massEigenbasis_sum_mul_sum_eq_site_inner (a mass : ℝ)
    (f g : FinLatticeField d N) :
    (∑ k : FinLatticeSites d N,
      (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x)) =
      ∑ x : FinLatticeSites d N, f x * g x := by
  let uf : EuclideanSpace ℝ (FinLatticeSites d N) :=
    (EuclideanSpace.equiv (FinLatticeSites d N) ℝ).symm f
  let ug : EuclideanSpace ℝ (FinLatticeSites d N) :=
    (EuclideanSpace.equiv (FinLatticeSites d N) ℝ).symm g
  have hparseval :=
    OrthonormalBasis.sum_inner_mul_inner (massEigenvectorBasis d N a mass) uf ug
  have hcoeff_left : ∀ k : FinLatticeSites d N,
      inner ℝ uf (massEigenvectorBasis d N a mass k) =
        ∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x := by
    intro k
    change (massEigenvectorBasis d N a mass k).ofLp ⬝ᵥ star uf.ofLp = _
    simp [dotProduct, star_trivial, uf, WithLp.ofLp_toLp]
  have hcoeff_right : ∀ k : FinLatticeSites d N,
      inner ℝ (massEigenvectorBasis d N a mass k) ug =
        ∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x := by
    intro k
    change ug.ofLp ⬝ᵥ star (massEigenvectorBasis d N a mass k).ofLp = _
    simp [dotProduct, star_trivial, ug, WithLp.ofLp_toLp, mul_comm]
  have hinner :
      inner ℝ uf ug = ∑ x : FinLatticeSites d N, f x * g x := by
    change ug.ofLp ⬝ᵥ star uf.ofLp = _
    simp [dotProduct, star_trivial, uf, ug, WithLp.ofLp_toLp, mul_comm]
  calc
    (∑ k : FinLatticeSites d N,
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x))
        = ∑ k : FinLatticeSites d N,
            inner ℝ uf (massEigenvectorBasis d N a mass k) *
              inner ℝ (massEigenvectorBasis d N a mass k) ug := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [hcoeff_left, hcoeff_right]
    _ = inner ℝ uf ug := hparseval
    _ = ∑ x : FinLatticeSites d N, f x * g x := hinner

/-- Spectral decomposition of the quadratic form of `massOperator`:
`∑ x, f x * (Q f) x = ∑ k, λ_k * c_k(f)^2`. -/
theorem massOperator_quadratic_eq_spectral (a mass : ℝ)
    (f : FinLatticeField d N) :
    (∑ x : FinLatticeSites d N, f x * (massOperator d N a mass f) x) =
      ∑ k : FinLatticeSites d N,
        massEigenvalues d N a mass k *
          (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) ^ 2 := by
  have hparseval :=
    massEigenbasis_sum_mul_sum_eq_site_inner (d := d) (N := N) a mass f (massOperator d N a mass f)
  have hcoeff :
      ∀ k : FinLatticeSites d N,
        (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
              (massOperator d N a mass f) x) =
          massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
    intro k
    exact massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff
      (d := d) (N := N) a mass f k
  calc
    (∑ x : FinLatticeSites d N, f x * (massOperator d N a mass f) x)
        = ∑ k : FinLatticeSites d N,
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                (massOperator d N a mass f) x) := by
            symm
            exact hparseval
    _ = ∑ k : FinLatticeSites d N,
          (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
            (massEigenvalues d N a mass k *
              (∑ x : FinLatticeSites d N,
                (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hcoeff k]
    _ = ∑ k : FinLatticeSites d N,
          massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring

/-- Eigenvalues of the mass operator are strictly positive.

Proof: Q is positive definite. For eigenvector e_k with eigenvalue λ_k:
`0 < ⟨e_k, Q e_k⟩ = λ_k ⟨e_k, e_k⟩ = λ_k`. -/
theorem massOperatorMatrix_eigenvalues_pos (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    0 < massEigenvalues d N a mass k := by
  let M : Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ := massOperatorMatrix d N a mass
  have hPosDef : M.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ?_
    refine ⟨massOperatorMatrix_isHermitian d N a mass, ?_⟩
    intro x hx
    have hpos := massOperator_pos_def d N a mass ha hmass x hx
    have hmul : M.mulVec x = massOperator d N a mass x := by
      ext i
      symm
      exact massOperator_eq_matrix_mulVec d N a mass x i
    simpa [M, dotProduct, hmul] using hpos
  have hEigPos : ∀ i : FinLatticeSites d N, 0 < (massMatrixHerm d N a mass).eigenvalues i :=
    (Matrix.IsHermitian.posDef_iff_eigenvalues_pos
      (hA := massMatrixHerm d N a mass)).mp hPosDef
  simpa [massEigenvalues] using hEigPos k



/-- The concrete finite-lattice spectral data used by the clean covariance. -/
def spectralData (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Pphi2Clean.Continuum.SpectralCovarianceData (FinLatticeSites d N) :=
  { eigenbasis := massEigenvectorBasis d N a mass
    eigenvalues := massEigenvalues d N a mass
    eigenvalues_pos := massOperatorMatrix_eigenvalues_pos d N a mass ha hmass }

end Pphi2Clean.UpstreamLattice
