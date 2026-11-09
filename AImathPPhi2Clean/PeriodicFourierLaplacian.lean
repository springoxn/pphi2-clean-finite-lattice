import AImathPPhi2Clean.ConcreteLatticeOperator
import Mathlib.Analysis.Fourier.ZMod

noncomputable section
namespace Pphi2Clean.UpstreamLattice
open ZMod

/-- The complex Fourier character on the finite periodic lattice indexed by a
momentum `p : Fin d → ZMod N`. -/
def periodicFourierCharacter (d N : ℕ) [NeZero N]
    (p x : FinLatticeSites d N) : ℂ :=
  ZMod.stdAddChar (∑ i : Fin d, p i * x i)

@[simp] theorem periodicFourierCharacter_zero (d N : ℕ) [NeZero N]
    (p : FinLatticeSites d N) : periodicFourierCharacter d N p 0 = 1 := by
  simp [periodicFourierCharacter]

theorem periodicFourierCharacter_update
    (d N : ℕ) [NeZero N] (p x : FinLatticeSites d N) (i : Fin d)
    (c : ZMod N) :
    periodicFourierCharacter d N p (fun j => if j = i then x j + c else x j) =
      ZMod.stdAddChar (p i * c) * periodicFourierCharacter d N p x := by
  unfold periodicFourierCharacter
  have hsum : (∑ j : Fin d, p j * (if j = i then x j + c else x j)) =
      (∑ j : Fin d, p j * x j) + p i * c := by
    calc
      (∑ j : Fin d, p j * (if j = i then x j + c else x j)) =
          ∑ j : Fin d, (p j * x j + if j = i then p j * c else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j = i <;> simp [h, mul_add]
      _ = (∑ j : Fin d, p j * x j) +
          ∑ j : Fin d, (if j = i then p j * c else 0) := Finset.sum_add_distrib
      _ = (∑ j : Fin d, p j * x j) + p i * c := by
        simp
  rw [hsum, AddChar.map_add_eq_mul]
  ring

/-- One-coordinate character orthogonality, including composite N. -/
theorem periodicFourierCharacter_sum_one (N : ℕ) [NeZero N] (p : ZMod N) :
    (∑ x : ZMod N, ZMod.stdAddChar (p * x)) =
      if p = 0 then (N : ℂ) else 0 := by
  simpa [mul_comm, ZMod.card] using
    AddChar.sum_mulShift p (ZMod.isPrimitive_stdAddChar N)

/-- The d-dimensional character is the tensor product of its coordinate
characters; no primality assumption on the lattice size is needed. -/
theorem periodicFourierCharacter_eq_prod (d N : ℕ) [NeZero N]
    (p x : FinLatticeSites d N) :
    periodicFourierCharacter d N p x =
      ∏ i : Fin d, ZMod.stdAddChar (p i * x i) := by
  unfold periodicFourierCharacter
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_succ, AddChar.map_add_eq_mul, Fin.prod_univ_succ]
    congr 1
    exact ih (fun i => p i.succ) (fun i => x i.succ)

/-- Exact finite character-sum factorization, the orthogonality kernel used
for Fourier inversion. -/
theorem periodicFourierCharacter_sum (d N : ℕ) [NeZero N]
    (p : FinLatticeSites d N) :
    (∑ x : FinLatticeSites d N, periodicFourierCharacter d N p x) =
      ∏ i : Fin d, (if p i = 0 then (N : ℂ) else 0) := by
  simp_rw [periodicFourierCharacter_eq_prod]
  rw [← Fintype.prod_sum (fun (i : Fin d) (x : ZMod N) =>
    ZMod.stdAddChar (p i * x))]
  simp_rw [periodicFourierCharacter_sum_one]

/-- Character-sum delta identity for all dimensions, including d = 0. -/
theorem periodicFourierCharacter_sum_delta (d N : ℕ) [NeZero N]
    (p : FinLatticeSites d N) :
    (∑ x : FinLatticeSites d N, periodicFourierCharacter d N p x) =
      if p = 0 then (N : ℂ) ^ d else 0 := by
  classical
  rw [periodicFourierCharacter_sum]
  by_cases hp : p = 0
  · simp [hp]
  · rw [if_neg hp]
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra h
      apply hp
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Multiplication of finite characters adds the momenta. -/
theorem periodicFourierCharacter_mul (d N : ℕ) [NeZero N]
    (p q x : FinLatticeSites d N) :
    periodicFourierCharacter d N p x * periodicFourierCharacter d N q x =
      periodicFourierCharacter d N (p + q) x := by
  simp only [periodicFourierCharacter, Pi.add_apply, add_mul,
    Finset.sum_add_distrib, AddChar.map_add_eq_mul]

/-- Algebraic Fourier orthogonality. The negative-frequency character is the
inverse-frequency factor; this form avoids a convention-dependent sign. -/
theorem periodicFourierCharacter_orthogonality (d N : ℕ) [NeZero N]
    (p q : FinLatticeSites d N) :
    (∑ x : FinLatticeSites d N,
      periodicFourierCharacter d N (-p) x * periodicFourierCharacter d N q x) =
      if p = q then (N : ℂ) ^ d else 0 := by
  simp_rw [periodicFourierCharacter_mul, periodicFourierCharacter_sum_delta]
  congr 1
  exact propext (by
    constructor
    · intro h
      have hh := congrArg (fun r => p + r) h
      simpa [← add_assoc] using hh.symm
    · intro h
      subst q
      simp)

 /-- A finite Fourier kernel with arbitrary spectral weights diagonalizes by
 two applications of character orthogonality. -/
theorem periodicFourierCharacter_weighted_kernel_pairing
    (d N : ℕ) [NeZero N]
    (k l : FinLatticeSites d N) (w : FinLatticeSites d N → ℂ) :
    ∑ p : FinLatticeSites d N, w p *
      (∑ x : FinLatticeSites d N,
        periodicFourierCharacter d N (-k) x * periodicFourierCharacter d N p x) *
      (∑ y : FinLatticeSites d N,
        periodicFourierCharacter d N (-p) y * periodicFourierCharacter d N l y) =
      if k = l then (N : ℂ) ^ (2 * d) * w k else 0 := by
  simp_rw [periodicFourierCharacter_orthogonality]
  by_cases h : k = l
  · subst l
    simp
    rw [show (2 * d) = d + d by omega, pow_add]
    ring
  · simp [h]
/-- Symmetry of the finite Fourier pairing. -/
theorem periodicFourierCharacter_swap (d N : ℕ) [NeZero N]
    (p x : FinLatticeSites d N) :
    periodicFourierCharacter d N p x = periodicFourierCharacter d N x p := by
  simp only [periodicFourierCharacter, mul_comm]

/-- Unnormalized finite Fourier coefficients with the negative phase. -/
def finiteFourierCoefficient (d N : ℕ) [NeZero N]
    (f : FinLatticeSites d N → ℂ) (p : FinLatticeSites d N) : ℂ :=
  ∑ y : FinLatticeSites d N, f y * periodicFourierCharacter d N (-p) y

/-- Finite Fourier inversion before dividing by the number of sites. -/
theorem finiteFourier_inversion_scaled (d N : ℕ) [NeZero N]
    (f : FinLatticeSites d N → ℂ) (x : FinLatticeSites d N) :
    (∑ p : FinLatticeSites d N,
      finiteFourierCoefficient d N f p * periodicFourierCharacter d N p x) =
      (N : ℂ) ^ d * f x := by
  classical
  unfold finiteFourierCoefficient
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  have hk (y : FinLatticeSites d N) :
      (∑ p : FinLatticeSites d N,
        periodicFourierCharacter d N (-p) y * periodicFourierCharacter d N p x) =
      if y = x then (N : ℂ) ^ d else 0 := by
    have he (p : FinLatticeSites d N) :
        periodicFourierCharacter d N (-p) y =
          periodicFourierCharacter d N (-y) p := by
      simp only [periodicFourierCharacter, Pi.neg_apply, neg_mul, mul_neg, mul_comm]
    simp_rw [he, periodicFourierCharacter_swap d N _ x]
    exact periodicFourierCharacter_orthogonality d N y x
  simp_rw [← Finset.mul_sum, hk]
  simp [mul_comm]

/-- Normalized inverse transform. In particular the characters span every
complex field on the finite torus. -/
theorem finiteFourier_inversion (d N : ℕ) [NeZero N]
    (f : FinLatticeSites d N → ℂ) (x : FinLatticeSites d N) :
    (N : ℂ)⁻¹ ^ d * (∑ p : FinLatticeSites d N,
      finiteFourierCoefficient d N f p * periodicFourierCharacter d N p x) =
      f x := by
  rw [finiteFourier_inversion_scaled, ← mul_assoc, ← mul_pow]
  simp

/-- Algebraic finite Parseval pairing with opposite frequencies. This
bilinear version applies to complex fields without a reality assumption. -/
theorem finiteFourier_bilinear_scaled (d N : ℕ) [NeZero N]
    (f g : FinLatticeSites d N → ℂ) :
    (∑ p : FinLatticeSites d N,
      finiteFourierCoefficient d N f (-p) * finiteFourierCoefficient d N g p) =
      (N : ℂ) ^ d * ∑ x : FinLatticeSites d N, f x * g x := by
  have hc (p : FinLatticeSites d N) :
      finiteFourierCoefficient d N f (-p) =
      ∑ x : FinLatticeSites d N, f x * periodicFourierCharacter d N p x := by
    simp [finiteFourierCoefficient]
  simp_rw [hc, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hi (x : FinLatticeSites d N) :
      (∑ p : FinLatticeSites d N, periodicFourierCharacter d N p x *
        finiteFourierCoefficient d N g p) = (N : ℂ) ^ d * g x := by
    simpa only [mul_comm] using finiteFourier_inversion_scaled d N g x
  simp_rw [hi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem finiteFourier_bilinear (d N : ℕ) [NeZero N]
    (f g : FinLatticeSites d N → ℂ) :
    (∑ x : FinLatticeSites d N, f x * g x) =
      (N : ℂ)⁻¹ ^ d * ∑ p : FinLatticeSites d N,
        finiteFourierCoefficient d N f (-p) * finiteFourierCoefficient d N g p := by
  rw [finiteFourier_bilinear_scaled, ← mul_assoc, ← mul_pow]
  simp

/-- Complex conjugation reverses the finite Fourier frequency. -/
theorem periodicFourierCharacter_star (d N : ℕ) [NeZero N]
    (p x : FinLatticeSites d N) :
    star (periodicFourierCharacter d N p x) =
      periodicFourierCharacter d N (-p) x := by
  have hs : (∑ i : Fin d, (-p) i * x i) = -(∑ i : Fin d, p i * x i) := by
    simp [Finset.sum_neg_distrib]
  change star (↑(ZMod.toCircle (∑ i : Fin d, p i * x i)) : ℂ) =
    ↑(ZMod.toCircle (∑ i : Fin d, (-p) i * x i))
  rw [hs, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

/-- Conjugating a field conjugates and reverses its Fourier coefficients. -/
theorem finiteFourierCoefficient_star_neg (d N : ℕ) [NeZero N]
    (f : FinLatticeSites d N → ℂ) (p : FinLatticeSites d N) :
    finiteFourierCoefficient d N (fun x => star (f x)) (-p) =
      star (finiteFourierCoefficient d N f p) := by
  simp only [finiteFourierCoefficient, neg_neg, star_sum, star_mul,
    periodicFourierCharacter_star, neg_neg, mul_comm]

/-- Hermitian finite Parseval identity with the same negative-phase convention
as the sampled covariance coefficients. -/
theorem finiteFourier_parseval (d N : ℕ) [NeZero N]
    (f g : FinLatticeSites d N → ℂ) :
    (∑ x : FinLatticeSites d N, star (f x) * g x) =
      (N : ℂ)⁻¹ ^ d * ∑ p : FinLatticeSites d N,
        star (finiteFourierCoefficient d N f p) * finiteFourierCoefficient d N g p := by
  simpa only [finiteFourierCoefficient_star_neg] using
    finiteFourier_bilinear d N (fun x => star (f x)) g

/-- The counting-measure squared-norm identity used in uniform Fourier-tail
estimates. It holds for every complex site field. -/
theorem finiteFourier_norm_sq (d N : ℕ) [NeZero N]
    (f : FinLatticeSites d N → ℂ) :
    (∑ p : FinLatticeSites d N, ‖finiteFourierCoefficient d N f p‖ ^ 2) =
      (N : ℝ) ^ d * ∑ x : FinLatticeSites d N, ‖f x‖ ^ 2 := by
  have h : (∑ p : FinLatticeSites d N,
      star (finiteFourierCoefficient d N f p) * finiteFourierCoefficient d N f p) =
      (N : ℂ) ^ d * ∑ x : FinLatticeSites d N, star (f x) * f x := by
    simpa only [finiteFourierCoefficient_star_neg] using
      finiteFourier_bilinear_scaled d N (fun x => star (f x)) f
  simp only [Complex.star_def, Complex.conj_mul'] at h
  exact_mod_cast h

/-- The one-coordinate periodic finite-difference eigenvalue. -/
def periodicFourierEigenvalue (d N : ℕ) [NeZero N]
    (a : ℝ) (p : FinLatticeSites d N) (i : Fin d) : ℂ :=
  (a : ℂ)⁻¹ ^ 2 *
    (ZMod.stdAddChar (p i) + ZMod.stdAddChar (-(p i)) - 2)

/-- The periodic finite-difference Laplacian acts diagonally on Fourier
characters. This is exact at finite N; it does not assert a continuum limit. -/
theorem complexFiniteLaplacian_character
    (d N : ℕ) [NeZero N] (a : ℝ) (p : FinLatticeSites d N)
    (x : FinLatticeSites d N) :
    (a : ℂ)⁻¹ ^ 2 * ∑ i : Fin d,
      (periodicFourierCharacter d N p (fun j => if j = i then x j + 1 else x j) +
       periodicFourierCharacter d N p (fun j => if j = i then x j - 1 else x j) -
       2 * periodicFourierCharacter d N p x) =
      (∑ i : Fin d, periodicFourierEigenvalue d N a p i) *
        periodicFourierCharacter d N p x := by
  have hplus (i : Fin d) := periodicFourierCharacter_update d N p x i 1
  have hminus (i : Fin d) :
      periodicFourierCharacter d N p (fun j => if j = i then x j - 1 else x j) =
        ZMod.stdAddChar (-(p i)) * periodicFourierCharacter d N p x := by
    simpa [sub_eq_add_neg, mul_neg_one] using
      periodicFourierCharacter_update d N p x i (-1 : ZMod N)
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hplus, hminus, periodicFourierEigenvalue, mul_one]
  ring

theorem complexFiniteMassOperator_character
    (d N : ℕ) [NeZero N] (a mass : ℝ) (p : FinLatticeSites d N)
    (x : FinLatticeSites d N) :
    -(a : ℂ)⁻¹ ^ 2 * ∑ i : Fin d,
      (periodicFourierCharacter d N p (fun j => if j = i then x j + 1 else x j) +
       periodicFourierCharacter d N p (fun j => if j = i then x j - 1 else x j) -
       2 * periodicFourierCharacter d N p x) +
      (mass : ℂ) ^ 2 * periodicFourierCharacter d N p x =
      ((mass : ℂ) ^ 2 - ∑ i : Fin d, periodicFourierEigenvalue d N a p i) *
        periodicFourierCharacter d N p x := by
  rw [neg_mul, complexFiniteLaplacian_character]
  ring

theorem complexFixedVolumeMassOperator_character
    (d N : ℕ) [NeZero N] (L mass : ℝ) (p : FinLatticeSites d N)
    (x : FinLatticeSites d N) :
    -(L / (N : ℝ) : ℂ)⁻¹ ^ 2 * ∑ i : Fin d,
      (periodicFourierCharacter d N p (fun j => if j = i then x j + 1 else x j) +
       periodicFourierCharacter d N p (fun j => if j = i then x j - 1 else x j) -
       2 * periodicFourierCharacter d N p x) +
      (mass : ℂ) ^ 2 * periodicFourierCharacter d N p x =
      ((mass : ℂ) ^ 2 - ∑ i : Fin d, periodicFourierEigenvalue d N (L / (N : ℝ)) p i) *
        periodicFourierCharacter d N p x := by
  simpa only [Complex.ofReal_div] using
    complexFiniteMassOperator_character d N (L / (N : ℝ)) mass p x


/-- Finite-mode convergence plus an `n`-uniform cutoff tail and convergence of
cutoff limits imply convergence of the untruncated sequence. The tail
hypothesis is intentionally explicit; applying this lemma to Fourier sums
requires a separate summable high-frequency estimate. -/
theorem tendsto_of_cutoff_tail
    (full : ℕ → ℝ) (cutoff : ℕ → ℕ → ℝ) (partialLimit : ℕ → ℝ) (target : ℝ)
    (hmode : ∀ K, Filter.Tendsto (fun n => cutoff n K) Filter.atTop
      (nhds (partialLimit K)))
    (htail : ∀ ε > 0, ∃ K₀, ∀ K ≥ K₀, ∀ n,
      |full n - cutoff n K| < ε)
    (hpartial : Filter.Tendsto partialLimit Filter.atTop (nhds target)) :
    Filter.Tendsto full Filter.atTop (nhds target) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨K₀, htailK⟩ := htail (ε / 3) hε3
  obtain ⟨K₁, hpartialK⟩ := (Metric.tendsto_atTop.1 hpartial) (ε / 3) hε3
  let K := max K₀ K₁
  have hK₀ : K₀ ≤ K := le_max_left _ _
  have hK₁ : K₁ ≤ K := le_max_right _ _
  obtain ⟨n₀, hmodeN⟩ := (Metric.tendsto_atTop.1 (hmode K)) (ε / 3) hε3
  refine ⟨n₀, ?_⟩
  intro n hn
  have ht := htailK K hK₀ n
  have hm := hmodeN n hn
  have hp := hpartialK K hK₁
  have htri : dist (full n) target ≤
      dist (full n) (cutoff n K) + dist (cutoff n K) (partialLimit K) +
        dist (partialLimit K) target := by
    calc
      dist (full n) target ≤ dist (full n) (cutoff n K) +
          dist (cutoff n K) target := dist_triangle _ _ _
      _ ≤ (dist (full n) (cutoff n K) + dist (cutoff n K) (partialLimit K)) +
          dist (partialLimit K) target := by
        have hT := dist_triangle (cutoff n K) (partialLimit K) target
        nlinarith [hT]
  have ht' : dist (full n) (cutoff n K) < ε / 3 := by
    simpa [Real.dist_eq] using ht
  have hm' : dist (cutoff n K) (partialLimit K) < ε / 3 := by
    simpa [Real.dist_eq] using hm
  have hp' : dist (partialLimit K) target < ε / 3 := by
    simpa [Real.dist_eq] using hp
  have hresult : dist (full n) target < ε := by
    linarith
  simpa using hresult

/-- The Fourier coefficient of a real part of a finite character is supported
at the two opposite frequencies, with their contributions merging when they
coincide (for example at zero or a Nyquist residue). -/
theorem finiteFourierCoefficient_character_re (d N : ℕ) [NeZero N]
    (k p : FinLatticeSites d N) :
    finiteFourierCoefficient d N
      (fun x => (periodicFourierCharacter d N k x).re) p =
      ((if p = k then (N : ℂ)^d else 0) +
        (if p = -k then (N : ℂ)^d else 0)) / 2 := by
  unfold finiteFourierCoefficient
  have hre (x : FinLatticeSites d N) :
      ((periodicFourierCharacter d N k x).re : ℂ) =
        (periodicFourierCharacter d N k x +
          starRingEnd ℂ (periodicFourierCharacter d N k x)) / 2 := by
    rw [Complex.add_conj]
    push_cast
    ring
  have hstar (x : FinLatticeSites d N) :
      starRingEnd ℂ (periodicFourierCharacter d N k x) =
        periodicFourierCharacter d N (-k) x := by
    simpa only [Complex.star_def] using periodicFourierCharacter_star d N k x
  calc
    (∑ x : FinLatticeSites d N,
      (↑(periodicFourierCharacter d N k x).re) * periodicFourierCharacter d N (-p) x) =
        (∑ x : FinLatticeSites d N,
          (periodicFourierCharacter d N k x * periodicFourierCharacter d N (-p) x +
            periodicFourierCharacter d N (-k) x * periodicFourierCharacter d N (-p) x) / 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hre, hstar]
      ring
    _ = ((∑ x : FinLatticeSites d N, periodicFourierCharacter d N (k + -p) x) +
          (∑ x : FinLatticeSites d N, periodicFourierCharacter d N (-k + -p) x)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      apply congrArg (fun z : ℂ => z / 2)
      apply congrArg₂ (fun a b : ℂ => a + b)
      · apply Finset.sum_congr rfl
        intro x hx
        rw [periodicFourierCharacter_mul]
      · apply Finset.sum_congr rfl
        intro x hx
        rw [periodicFourierCharacter_mul]
    _ = _ := by
      rw [periodicFourierCharacter_sum_delta, periodicFourierCharacter_sum_delta]
      have h1 : k + -p = 0 ↔ p = k := by
        constructor
        · intro h
          have hh := congrArg (fun q : FinLatticeSites d N => q + p) h
          simpa [add_assoc] using hh.symm
        · intro h
          subst p
          simp
      have h2 : -k + -p = 0 ↔ p = -k := by
        constructor
        · intro h
          have hn : -(k + p) = 0 := by simpa only [neg_add] using h
          have hh : k + p = 0 := neg_eq_zero.mp hn
          exact eq_neg_of_add_eq_zero_right hh
        · intro h
          subst p
          simp
      simp [h1, h2]

/-- Imaginary character coefficients have opposite signs at opposite frequencies. -/
theorem finiteFourierCoefficient_character_im (d N : ℕ) [NeZero N]
    (k p : FinLatticeSites d N) :
    finiteFourierCoefficient d N
      (fun x => (periodicFourierCharacter d N k x).im) p =
      ((if p = k then (N : ℂ)^d else 0) -
        (if p = -k then (N : ℂ)^d else 0)) / (2 * Complex.I) := by
  unfold finiteFourierCoefficient
  have him (x : FinLatticeSites d N) :
      ((periodicFourierCharacter d N k x).im : ℂ) =
        (periodicFourierCharacter d N k x -
          starRingEnd ℂ (periodicFourierCharacter d N k x)) / (2 * Complex.I) := by
    rw [Complex.sub_conj]
    push_cast
    field_simp
  have hstar (x : FinLatticeSites d N) :
      starRingEnd ℂ (periodicFourierCharacter d N k x) =
        periodicFourierCharacter d N (-k) x := by
    change star (periodicFourierCharacter d N k x) = _
    rw [periodicFourierCharacter_star]
  calc
    (∑ x : FinLatticeSites d N,
      (↑(periodicFourierCharacter d N k x).im) * periodicFourierCharacter d N (-p) x) =
        (∑ x : FinLatticeSites d N,
          (periodicFourierCharacter d N k x * periodicFourierCharacter d N (-p) x -
            periodicFourierCharacter d N (-k) x * periodicFourierCharacter d N (-p) x) / (2 * Complex.I)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [him, hstar]
      ring
    _ = ((∑ x : FinLatticeSites d N, periodicFourierCharacter d N (k + -p) x) -
          (∑ x : FinLatticeSites d N, periodicFourierCharacter d N (-k + -p) x)) / (2 * Complex.I) := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      apply congrArg (fun z : ℂ => z / (2 * Complex.I))
      apply congrArg₂ (fun a b : ℂ => a - b)
      · apply Finset.sum_congr rfl
        intro x hx
        rw [periodicFourierCharacter_mul]
      · apply Finset.sum_congr rfl
        intro x hx
        rw [periodicFourierCharacter_mul]
    _ = _ := by
      rw [periodicFourierCharacter_sum_delta, periodicFourierCharacter_sum_delta]
      have h1 : k + -p = 0 ↔ p = k := by
        constructor
        · intro h
          have hh := congrArg (fun q : FinLatticeSites d N => q + p) h
          simpa [add_assoc] using hh.symm
        · intro h
          subst p
          simp
      have h2 : -k + -p = 0 ↔ p = -k := by
        constructor
        · intro h
          have hh : k + p = 0 := by
            have hn := neg_eq_zero.mpr (show -k + -p = 0 from h)
            simpa only [neg_add, neg_neg, neg_zero] using hn
          exact eq_neg_of_add_eq_zero_right hh
        · intro h
          subst p
          simp
      simp [h1, h2]
