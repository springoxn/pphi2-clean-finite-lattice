import AImathPPhi2Clean.PhysicalLatticeGaussianLaw
import AImathPPhi2Clean.PeriodicFourierLaplacian
import AImathPPhi2Clean.FourierMassResolvent
import AImathPPhi2Clean.PeriodicFrequencyBox
import AImathPPhi2Clean.PhysicalCellRiemann
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace Pphi2Clean.Continuum
open Pphi2Clean.UpstreamLattice MeasureTheory ProbabilityTheory

/-- Periodicity condition for a real test function on the flat torus of side
length `L`: translating by one period in any coordinate leaves its lift on
`ℝ^d` unchanged. -/
def IsFlatTorusPeriodic (d : ℕ) (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) : Prop :=
  ∀ (x : Fin d → ℝ) (i : Fin d),
    f (fun j => if j = i then x j + L else x j) = f x

/-- Integral-normalized discrete Fourier coefficient. The cell volume is
included here, not in the Fourier character. -/
def sampledFourierCoefficient (d N : ℕ) [NeZero N] (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (p : FinLatticeSites d N) : ℂ :=
  ((L / (N : ℝ)) ^ d : ℝ) *
    ∑ x : FinLatticeSites d N,
      (f (latticePhysicalPoint d N (L / (N : ℝ)) x) : ℂ) *
        periodicFourierCharacter d N (-p) x

/-- Exact character-valued mass symbol from the finite eigenfunction theorem.
Its real sine-squared identification is proved below. -/
def fixedVolumeMassSymbol (d N : ℕ) [NeZero N] (L mass : ℝ)
    (p : FinLatticeSites d N) : ℂ :=
  (mass : ℂ) ^ 2 - ∑ i : Fin d,
    periodicFourierEigenvalue d N (L / (N : ℝ)) p i

/-- Real nonnegative nearest-neighbor dispersion written using residue values. -/
def fixedVolumeMassSymbolReal (d N : ℕ) [NeZero N] (L mass : ℝ)
    (p : FinLatticeSites d N) : ℝ :=
  mass ^ 2 + 4 * (L / (N : ℝ))⁻¹ ^ 2 *
    ∑ i : Fin d, Real.sin (Real.pi * ((p i).val : ℝ) / (N : ℝ)) ^ 2

/-- Opposite residues are conjugate character values. -/
theorem stdAddChar_neg_eq_conj {N : ℕ} [NeZero N] (p : ZMod N) :
    ZMod.stdAddChar (-p) = star (ZMod.stdAddChar p) := by
  change (↑(ZMod.toCircle (-p)) : ℂ) = star (↑(ZMod.toCircle p) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

/-- Exact trigonometric identity for one coordinate, valid including Nyquist
and the one-site lattice. -/
theorem stdAddChar_add_neg_sub_two {N : ℕ} [NeZero N] (p : ZMod N) :
    ZMod.stdAddChar p + ZMod.stdAddChar (-p) - 2 =
      (-4 * Real.sin (Real.pi * (p.val : ℝ) / (N : ℝ)) ^ 2 : ℝ) := by
  have hr : (ZMod.stdAddChar p).re = Real.cos (2 * (Real.pi * (p.val : ℝ) / (N : ℝ))) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp,
      Complex.exp_ofReal_mul_I_re]
    congr 1
    ring
  rw [stdAddChar_neg_eq_conj]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re,
      Complex.ofReal_re, Complex.re_ofNat]
    rw [hr, Real.cos_two_mul_eq_one_sub]
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.star_def, Complex.conj_im,
      Complex.ofReal_im, Complex.im_ofNat]
    ring

/-- The character mass symbol is exactly the real sine-squared dispersion. -/
theorem fixedVolumeMassSymbol_eq_real
    (d N : ℕ) [NeZero N] (L mass : ℝ) (p : FinLatticeSites d N) :
    fixedVolumeMassSymbol d N L mass p = (fixedVolumeMassSymbolReal d N L mass p : ℂ) := by
  unfold fixedVolumeMassSymbol periodicFourierEigenvalue fixedVolumeMassSymbolReal
  simp_rw [stdAddChar_add_neg_sub_two]
  push_cast
  rw [Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Explicit physical sine-squared formula with frequency scale N/L. -/
theorem fixedVolumeMassSymbol_eq_sin_sq
    (d N : ℕ) [NeZero N] (L mass : ℝ) (p : FinLatticeSites d N) :
    fixedVolumeMassSymbol d N L mass p =
      (mass ^ 2 + 4 * ((N : ℝ) / L) ^ 2 *
        ∑ i : Fin d, Real.sin (Real.pi * ((p i).val : ℝ) / (N : ℝ)) ^ 2 : ℝ) := by
  simpa only [fixedVolumeMassSymbolReal, inv_div] using
    fixedVolumeMassSymbol_eq_real d N L mass p

/-- Mass positivity alone gives positivity of the real dispersion. -/
theorem fixedVolumeMassSymbolReal_pos
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hmass : 0 < mass) (p : FinLatticeSites d N) :
    0 < fixedVolumeMassSymbolReal d N L mass p := by
  unfold fixedVolumeMassSymbolReal
  have hs : 0 ≤ ∑ i : Fin d, Real.sin (Real.pi * ((p i).val : ℝ) / (N : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  positivity

/-- Jordan's chord bound in lattice-frequency variables. The closed endpoint
allows the even-lattice Nyquist frequency. -/
theorem two_mul_div_le_sin_pi_mul_div
    (x n : ℝ) (hn : 0 < n) (hx : 0 ≤ x) (hhalf : 2 * x ≤ n) :
    2 * x / n ≤ Real.sin (Real.pi * x / n) := by
  have harg : 0 ≤ 2 * x / n := div_nonneg (by positivity) hn.le
  have hone : 2 * x / n ≤ 1 := (div_le_one hn).mpr hhalf
  have h := Real.le_sin_mul harg hone
  convert h using 1 <;> congr 1 <;> ring

/-- Reflection of frequencies above N/2 gives the periodic distance version
of the chord bound, without excluding N=1 or Nyquist endpoints. -/
theorem stdAddChar_frequency_sin_lower
    {N : ℕ} [NeZero N] (p : ZMod N) :
    2 * (min p.val (N - p.val) : ℕ) / (N : ℝ) ≤
      Real.sin (Real.pi * (p.val : ℝ) / (N : ℝ)) := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hv : p.val ≤ N := (ZMod.val_lt p).le
  have hsub : ((N - p.val : ℕ) : ℝ) = (N : ℝ) - (p.val : ℝ) := by
    exact_mod_cast (Nat.cast_sub hv : ((N - p.val : ℕ) : ℝ) = _)
  rcases le_total p.val (N - p.val) with hp | hp
  · rw [min_eq_left hp]
    apply two_mul_div_le_sin_pi_mul_div _ _ hn (Nat.cast_nonneg _)
    have hh : (p.val : ℝ) ≤ ((N - p.val : ℕ) : ℝ) := by exact_mod_cast hp
    rw [hsub] at hh
    linarith
  · rw [min_eq_right hp]
    have hh : ((N - p.val : ℕ) : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast hp
    have hc := two_mul_div_le_sin_pi_mul_div
      ((N - p.val : ℕ) : ℝ) (N : ℝ) hn (Nat.cast_nonneg _)
      (by rw [hsub] at hh ⊢; linarith)
    have heq : Real.pi * ((N - p.val : ℕ) : ℝ) / (N : ℝ) =
        Real.pi - Real.pi * (p.val : ℝ) / (N : ℝ) := by
      rw [hsub]
      field_simp
      <;> ring
    rw [heq, Real.sin_pi_sub] at hc
    exact hc

/-- Quantitative dispersion bound for each periodic frequency coordinate.
This form directly controls the complement of the existing box cutoff. -/
theorem fixedVolumeMassSymbolReal_ge_coordinate
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L)
    (p : FinLatticeSites d N) (i : Fin d) :
    mass ^ 2 + 16 * (min (p i).val (N - (p i).val) : ℕ) ^ 2 / L ^ 2 ≤
      fixedVolumeMassSymbolReal d N L mass p := by
  let r : ℝ := (min (p i).val (N - (p i).val) : ℕ)
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hc := stdAddChar_frequency_sin_lower (p i)
  have hz : 0 ≤ 2 * r / (N : ℝ) := by positivity
  have hsq : (2 * r / (N : ℝ)) ^ 2 ≤
      Real.sin (Real.pi * ((p i).val : ℝ) / (N : ℝ)) ^ 2 := by
    change 2 * r / (N : ℝ) ≤ _ at hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (add_nonneg (le_trans hz hc) hz)]
  have hsum : Real.sin (Real.pi * ((p i).val : ℝ) / (N : ℝ)) ^ 2 ≤
      ∑ j : Fin d, Real.sin (Real.pi * ((p j).val : ℝ) / (N : ℝ)) ^ 2 :=
    Finset.single_le_sum
      (f := fun j : Fin d => Real.sin (Real.pi * ((p j).val : ℝ) / (N : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hmul := mul_le_mul_of_nonneg_left (hsq.trans hsum)
    (show 0 ≤ 4 * (L / (N : ℝ))⁻¹ ^ 2 by positivity)
  have hid : 4 * (L / (N : ℝ))⁻¹ ^ 2 * (2 * r / (N : ℝ)) ^ 2 =
      16 * r ^ 2 / L ^ 2 := by
    field_simp
    <;> ring
  rw [hid] at hmul
  unfold fixedVolumeMassSymbolReal
  dsimp [r] at hmul
  linarith only [hmul]

/-- Outside the existing symmetric box cutoff the denominator has a bound
uniform in N. In dimension zero the premise is false, so no exception is needed. -/
theorem fixedVolumeMassSymbolReal_ge_outside_cutoff
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L)
    (p : FinLatticeSites d N) (K : ℕ)
    (hout : ¬ (∀ i : Fin d, min (p i).val (N - (p i).val) ≤ K)) :
    mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2 ≤ fixedVolumeMassSymbolReal d N L mass p := by
  push_neg at hout
  obtain ⟨i, hi⟩ := hout
  have hc := fixedVolumeMassSymbolReal_ge_coordinate d N L mass hL p i
  calc
    mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2 ≤
        mass ^ 2 + 16 * (min (p i).val (N - (p i).val) : ℕ) ^ 2 / L ^ 2 := by
      gcongr
    _ ≤ _ := hc

/-- Maximum periodic frequency distance, with value zero in dimension zero. -/
def periodicFrequencyRadius (d N : ℕ) [NeZero N] (p : FinLatticeSites d N) : ℕ :=
  Finset.univ.sup (fun i : Fin d => min (p i).val (N - (p i).val))

/-- The radius is exactly the frequency-box predicate already used by cutoff. -/
theorem periodicFrequencyRadius_le_iff (d N : ℕ) [NeZero N]
    (p : FinLatticeSites d N) (K : ℕ) :
    periodicFrequencyRadius d N p ≤ K ↔
      ∀ i : Fin d, min (p i).val (N - (p i).val) ≤ K := by
  simp [periodicFrequencyRadius, Finset.sup_le_iff]

/-- Quantitative lower bound at the maximum periodic frequency, for all d,N. -/
theorem fixedVolumeMassSymbolReal_ge_radius
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (p : FinLatticeSites d N) :
    mass ^ 2 + 16 * (periodicFrequencyRadius d N p : ℝ) ^ 2 / L ^ 2 ≤
      fixedVolumeMassSymbolReal d N L mass p := by
  by_cases hd : d = 0
  · subst d
    simp [periodicFrequencyRadius, fixedVolumeMassSymbolReal]
  · haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
      Finset.univ_nonempty (fun i : Fin d => min (p i).val (N - (p i).val))
    unfold periodicFrequencyRadius
    rw [heq]
    exact fixedVolumeMassSymbolReal_ge_coordinate d N L mass hL p i

@[simp] theorem fixedVolumeMassSymbol_zero (d N : ℕ) [NeZero N]
    (L mass : ℝ) : fixedVolumeMassSymbol d N L mass 0 = (mass : ℂ) ^ 2 := by
  norm_num [fixedVolumeMassSymbol, periodicFourierEigenvalue]


/-- The finite nearest-neighbor mass symbol is invariant under frequency negation. -/
theorem fixedVolumeMassSymbol_neg (d N : ℕ) [NeZero N] (L mass : ℝ)
    (p : FinLatticeSites d N) :
    fixedVolumeMassSymbol d N L mass (-p) =
      fixedVolumeMassSymbol d N L mass p := by
  have hev (i : Fin d) :
      periodicFourierEigenvalue d N (L / (N : ℝ)) (-p) i =
        periodicFourierEigenvalue d N (L / (N : ℝ)) p i := by
    simp only [periodicFourierEigenvalue, Pi.neg_apply, neg_neg]
    ring
  unfold fixedVolumeMassSymbol
  congr 1
  exact Finset.sum_congr rfl (fun i hi => hev i)


/-- Exact finite Fourier resolvent pairing with integral-normalized coefficients.
Equality with the actual GJ covariance is proved below. -/
def discreteFourierGreenPairing (d N : ℕ) [NeZero N] (L mass : ℝ)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) : ℂ :=
  (L : ℂ)⁻¹ ^ d * ∑ p : FinLatticeSites d N,
    star (sampledFourierCoefficient d N L f p) *
      sampledFourierCoefficient d N L g p / fixedVolumeMassSymbol d N L mass p

/-- Integer modes reduce modulo N without choosing a representative. -/
def integerLatticeMode (d N : ℕ) (k : Fin d → ℤ) : FinLatticeSites d N :=
  fun i => (k i : ZMod N)

/-- Signed integer version of the exact coordinate symbol; no large-N
representative convention or separate negative-frequency case is needed. -/
theorem stdAddChar_intCast_add_neg_sub_two
    {N : ℕ} [NeZero N] (k : ℤ) :
    ZMod.stdAddChar (k : ZMod N) + ZMod.stdAddChar (-(k : ZMod N)) - 2 =
      (-4 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2 : ℝ) := by
  have hr : (ZMod.stdAddChar (k : ZMod N)).re =
      Real.cos (2 * (Real.pi * (k : ℝ) / (N : ℝ))) := by
    rw [ZMod.stdAddChar_coe]
    have heq : 2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ) =
        ((2 * (Real.pi * (k : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [heq, Complex.exp_ofReal_mul_I_re]
  rw [stdAddChar_neg_eq_conj]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re,
      Complex.ofReal_re, Complex.re_ofNat]
    rw [hr, Real.cos_two_mul_eq_one_sub]
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.star_def, Complex.conj_im,
      Complex.ofReal_im, Complex.im_ofNat]
    ring

/-- Exact signed-mode dispersion, valid for every N, even when modes wrap. -/
theorem fixedVolumeMassSymbol_integerLatticeMode
    (d N : ℕ) [NeZero N] (L mass : ℝ) (k : Fin d → ℤ) :
    fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k) =
      (mass ^ 2 + 4 * ((N : ℝ) / L) ^ 2 *
        ∑ i : Fin d, Real.sin (Real.pi * (k i : ℝ) / (N : ℝ)) ^ 2 : ℝ) := by
  unfold fixedVolumeMassSymbol periodicFourierEigenvalue integerLatticeMode
  simp_rw [stdAddChar_intCast_add_neg_sub_two]
  push_cast
  rw [Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [inv_div]
  ring

/-- The scaled sine is a continuous sinc expression, including k=0. -/
theorem scaled_sin_eq_sinc
    (N : ℕ) [NeZero N] (L : ℝ) (k : ℤ) :
    ((N : ℝ) / L) * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) =
      (Real.pi * (k : ℝ) / L) * Real.sinc (Real.pi * (k : ℝ) / (N : ℝ)) := by
  by_cases hk : k = 0
  · simp [hk]
  · have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have harg : Real.pi * (k : ℝ) / (N : ℝ) ≠ 0 :=
      div_ne_zero (mul_ne_zero Real.pi_ne_zero hkr) (Nat.cast_ne_zero.mpr (NeZero.ne N))
    rw [Real.sinc_of_ne_zero harg]
    field_simp
    <;> ring

/-- A sinc formula makes the fixed-integer-mode limit independent of residue
representatives and of signs of the mode coordinates. -/
theorem fixedVolumeMassSymbol_integerLatticeMode_sinc
    (d N : ℕ) [NeZero N] (L mass : ℝ) (k : Fin d → ℤ) :
    fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k) =
      (mass ^ 2 + 4 * ∑ i : Fin d,
        ((Real.pi * (k i : ℝ) / L) * Real.sinc (Real.pi * (k i : ℝ) / (N : ℝ))) ^ 2 : ℝ) := by
  rw [fixedVolumeMassSymbol_integerLatticeMode]
  congr 1
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc]
  calc
    _ = 4 * (((N : ℝ) / L) * Real.sin (Real.pi * (k i : ℝ) / (N : ℝ))) ^ 2 := by ring
    _ = _ := by rw [scaled_sin_eq_sinc]

/-- The continuous Fourier phase uses physical coordinates of period L. -/
def torusFourierPhase (d : ℕ) (L : ℝ) (k : Fin d → ℤ)
    (x : Fin d → ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi / L) * ∑ i : Fin d, (k i : ℝ) * x i : ℝ) *
    Complex.I)

/-- Integer lifts remove every choice of residue representative from the phase. -/
theorem periodicFourierCharacter_integerLatticeMode
    (d N : ℕ) [NeZero N] (k : Fin d → ℤ) (x : FinLatticeSites d N) :
    periodicFourierCharacter d N (integerLatticeMode d N k) x =
      Complex.exp (2 * Real.pi * Complex.I *
        (∑ i : Fin d, (k i : ℂ) * ((x i).val : ℂ)) / (N : ℂ)) := by
  have hcast : (↑(∑ i : Fin d, k i * ((x i).val : ℤ)) : ZMod N) =
      ∑ i : Fin d, (k i : ZMod N) * x i := by
    push_cast
    simp
  unfold periodicFourierCharacter integerLatticeMode
  rw [← hcast, ZMod.stdAddChar_coe]
  push_cast
  rfl

/-- At physical sample points the finite character is exactly the continuous
phase. This includes negative integer frequencies without a size restriction. -/
theorem periodicFourierCharacter_eq_torusFourierPhase
    (d N : ℕ) [NeZero N] (L : ℝ) (hL : L ≠ 0)
    (k : Fin d → ℤ) (x : FinLatticeSites d N) :
    periodicFourierCharacter d N (integerLatticeMode d N k) x =
      torusFourierPhase d L k (latticePhysicalPoint d N (L / (N : ℝ)) x) := by
  rw [periodicFourierCharacter_integerLatticeMode]
  unfold torusFourierPhase latticePhysicalPoint
  congr 1
  have hsum : (∑ i : Fin d, (k i : ℝ) * (L / (N : ℝ) * ((x i).val : ℝ))) =
      (L / (N : ℝ)) * ∑ i : Fin d, (k i : ℝ) * ((x i).val : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  push_cast
  field_simp [show (L : ℂ) ≠ 0 by exact_mod_cast hL]
  <;> ring

/-- Exact quadrature formula with the negative phase used by the continuous
Fourier coefficient. No periodicity or asymptotic identification is assumed. -/
theorem sampledFourierCoefficient_integerLatticeMode
    (d N : ℕ) [NeZero N] (L : ℝ) (hL : L ≠ 0)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (k : Fin d → ℤ) :
    sampledFourierCoefficient d N L f (integerLatticeMode d N k) =
      ((L / (N : ℝ)) ^ d : ℝ) * ∑ x : FinLatticeSites d N,
        (f (latticePhysicalPoint d N (L / (N : ℝ)) x) : ℂ) *
          torusFourierPhase d L (-k) (latticePhysicalPoint d N (L / (N : ℝ)) x) := by
  unfold sampledFourierCoefficient
  have hneg : -integerLatticeMode d N k = integerLatticeMode d N (-k) := by
    ext i
    simp [integerLatticeMode]
  rw [hneg]
  simp_rw [periodicFourierCharacter_eq_torusFourierPhase d N L hL]

/-- Complex conjugation of a periodic Fourier phase reverses the integer mode. -/
theorem torusFourierPhase_star_eq_neg
    (d : ℕ) (L : ℝ) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    star (torusFourierPhase d L k x) = torusFourierPhase d L (-k) x := by
  unfold torusFourierPhase
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I, Finset.sum_neg_distrib]
  left
  simp only [map_ofNat]

/-- Lebesgue integral on the physical coordinate cell, not probability Haar
measure. Periodic tests are the lifts satisfying `IsFlatTorusPeriodic`. -/
def torusFourierCoefficient (d : ℕ) (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (k : Fin d → ℤ) : ℂ :=
  ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) L),
    (f x : ℂ) * torusFourierPhase d L (-k) x

/-- Real-valued test functions have conjugate Fourier coefficients at opposite modes. -/
theorem torusFourierCoefficient_star_eq_neg
    (d : ℕ) (L : ℝ) (f : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (k : Fin d → ℤ) :
    star (torusFourierCoefficient d L f k) =
      torusFourierCoefficient d L f (-k) := by
  unfold torusFourierCoefficient
  change (starRingEnd ℂ) (∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) L),
      (f x : ℂ) * torusFourierPhase d L (-k) x) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, Complex.conj_ofReal]
  change (f x : ℂ) * star (torusFourierPhase d L (-k) x) =
    (f x : ℂ) * torusFourierPhase d L (-(-k)) x
  rw [torusFourierPhase_star_eq_neg]

/-- The sampled Fourier coefficients converge to the physically normalized
cell integral at every fixed signed integer mode. Continuity suffices here. -/
theorem sampledFourierCoefficient_integerLatticeMode_tendsto
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (k : Fin d → ℤ) :
    Filter.Tendsto (fun n : ℕ => sampledFourierCoefficient d (n + 1) L f
      (integerLatticeMode d (n + 1) k)) Filter.atTop
      (nhds (torusFourierCoefficient d L f k)) := by
  let H : (Fin d → ℝ) → ℂ := fun x => (f x : ℂ) * torusFourierPhase d L (-k) x
  have hc : Continuous H := by
    dsimp [H, torusFourierPhase]
    fun_prop
  have hh := physicalCell_riemann_sum_tendsto d L hL H hc
  have heq (n : ℕ) : sampledFourierCoefficient d (n + 1) L f
      (integerLatticeMode d (n + 1) k) =
      (L / ((n + 1 : ℕ) : ℝ)) ^ d •
        ∑ q : Fin d → Fin (n + 1), H (fun i =>
          L / ((n + 1 : ℕ) : ℝ) * ((q i).val : ℝ)) := by
    rw [sampledFourierCoefficient_integerLatticeMode d (n + 1) L hL.ne']
    rw [Complex.real_smul]
    congr 1
  simpa only [heq, torusFourierCoefficient, H] using hh

/-- Positive continuum resolvent denominator for mass > 0. -/
def torusMassSymbol (d : ℕ) (L mass : ℝ) (k : Fin d → ℤ) : ℝ :=
  mass ^ 2 + (2 * Real.pi / L) ^ 2 * ∑ i : Fin d, (k i : ℝ) ^ 2

/-- Fixed signed integer modes have the continuum mass-symbol limit. -/
theorem fixedVolumeMassSymbol_integerLatticeMode_tendsto
    (d : ℕ) (L mass : ℝ) (k : Fin d → ℤ) :
    Filter.Tendsto (fun n : ℕ =>
      fixedVolumeMassSymbol d (n + 1) L mass (integerLatticeMode d (n + 1) k))
      Filter.atTop (nhds (torusMassSymbol d L mass k : ℂ)) := by
  have hcoord (i : Fin d) : Filter.Tendsto
      (fun n : ℕ => ((Real.pi * (k i : ℝ) / L) *
        Real.sinc (Real.pi * (k i : ℝ) / ((n + 1 : ℕ) : ℝ))) ^ 2)
      Filter.atTop (nhds ((Real.pi * (k i : ℝ) / L) ^ 2)) := by
    have hz : Filter.Tendsto
        (fun n : ℕ => Real.pi * (k i : ℝ) / ((n + 1 : ℕ) : ℝ))
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have hs := (Real.continuous_sinc.tendsto 0).comp hz
    simpa using (tendsto_const_nhds.mul hs).pow 2
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => hcoord i)
  have hall : Filter.Tendsto
      (fun n : ℕ => mass ^ 2 + 4 * ∑ i : Fin d,
        ((Real.pi * (k i : ℝ) / L) * Real.sinc (Real.pi * (k i : ℝ) / ((n + 1 : ℕ) : ℝ))) ^ 2)
      Filter.atTop (nhds (mass ^ 2 + 4 * ∑ i : Fin d, (Real.pi * (k i : ℝ) / L) ^ 2)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hsum)
  have htarget : mass ^ 2 + 4 * ∑ i : Fin d, (Real.pi * (k i : ℝ) / L) ^ 2 =
      torusMassSymbol d L mass k := by
    unfold torusMassSymbol
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hall
  simp_rw [htarget] at hc
  simpa only [fixedVolumeMassSymbol_integerLatticeMode_sinc, Function.comp_def] using hc

/-- Positive continuum mass permits inversion of the fixed-mode limit. -/
theorem fixedVolumeMassSymbol_integerLatticeMode_inv_tendsto
    (d : ℕ) (L mass : ℝ) (hmass : 0 < mass) (k : Fin d → ℤ) :
    Filter.Tendsto (fun n : ℕ =>
      (fixedVolumeMassSymbol d (n + 1) L mass (integerLatticeMode d (n + 1) k))⁻¹)
      Filter.atTop (nhds (torusMassSymbol d L mass k : ℂ)⁻¹) := by
  apply (fixedVolumeMassSymbol_integerLatticeMode_tendsto d L mass k).inv₀
  have hp : 0 < torusMassSymbol d L mass k := by
    unfold torusMassSymbol
    have hs : 0 ≤ ∑ i : Fin d, (k i : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hnon := mul_nonneg (sq_nonneg (2 * Real.pi / L)) hs
    nlinarith [sq_pos_of_pos hmass]
  exact_mod_cast hp.ne'

@[simp] theorem torusMassSymbol_zero (d : ℕ) (L mass : ℝ) :
    torusMassSymbol d L mass 0 = mass ^ 2 := by
  simp [torusMassSymbol]

theorem torusMassSymbol_pos (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (k : Fin d → ℤ) : 0 < torusMassSymbol d L mass k := by
  unfold torusMassSymbol
  have hs : 0 ≤ ∑ i : Fin d, (k i : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hp := mul_nonneg (sq_nonneg (2 * Real.pi / L)) hs
  nlinarith [sq_pos_of_pos hmass]

/-- The explicit Fourier Green series. Absolute summability and its use as the
actual lattice covariance limit are proved below. Identification with an
independently defined continuum resolvent is a separate operator theorem. -/
def torusFourierGreenPairing (d : ℕ) (L mass : ℝ)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) : ℂ :=
  (L : ℂ)⁻¹ ^ d * ∑' k : Fin d → ℤ,
    star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
      (torusMassSymbol d L mass k : ℂ)

/-- Symmetric-frequency cutoff: distance of a residue to zero is the
minimum of its two nonnegative representatives. -/
def discreteFourierGreenCutoff (d N : ℕ) [NeZero N] (L mass : ℝ)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) : ℂ :=
  (L : ℂ)⁻¹ ^ d * ∑ p : FinLatticeSites d N,
    if (∀ i : Fin d, min (p i).val (N - (p i).val) ≤ K) then
      star (sampledFourierCoefficient d N L f p) *
        sampledFourierCoefficient d N L g p / fixedVolumeMassSymbol d N L mass p
    else 0

/-- Exact large-N frequency-box reindexing for the existing discrete cutoff. -/
theorem discreteFourierGreenCutoff_eq_integer_box
    (d N : ℕ) [NeZero N] (L mass : ℝ)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) (hN : 2 * K < N) :
    discreteFourierGreenCutoff d N L mass f g K =
      (L : ℂ)⁻¹ ^ d * ∑ q : Fin d → Fin (2 * K + 1),
        let k : Fin d → ℤ := fun i => (q i).val - (K : ℤ)
        star (sampledFourierCoefficient d N L f (integerLatticeMode d N k)) *
          sampledFourierCoefficient d N L g (integerLatticeMode d N k) /
            fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k) := by
  unfold discreteFourierGreenCutoff
  rw [periodicFrequencyBox_sum d N K hN]
  rfl

/-- Each integer mode in [-K,K]^d occurs once in this finite box. -/
def torusFourierGreenCutoff (d : ℕ) (L mass : ℝ)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) : ℂ :=
  (L : ℂ)⁻¹ ^ d * ∑ q : Fin d → Fin (2 * K + 1),
    let k : Fin d → ℤ := fun i => (q i).val - (K : ℤ)
    star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
      (torusMassSymbol d L mass k : ℂ)

/-- Fourier coefficients of the actual physically weighted site test field
are exactly the integral-normalized sampled coefficients. -/
theorem finiteFourierCoefficient_physical_sample
    (d N : ℕ) [NeZero N] (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (p : FinLatticeSites d N) :
    finiteFourierCoefficient d N
      (fun x => (((L / (N : ℝ)) ^ d * f (latticePhysicalPoint d N (L / (N : ℝ)) x) : ℝ) : ℂ)) p =
      sampledFourierCoefficient d N L f p := by
  simp [finiteFourierCoefficient, sampledFourierCoefficient, Finset.mul_sum, mul_assoc]

/-- Exact Parseval equality in physical-volume normalization, including every
lattice size and dimension. -/
theorem sampledFourierCoefficient_parseval
    (d N : ℕ) [NeZero N] (L : ℝ)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    (∑ p : FinLatticeSites d N, ‖sampledFourierCoefficient d N L f p‖ ^ 2) =
      L ^ d * ((L / (N : ℝ)) ^ d * ∑ x : FinLatticeSites d N,
        (f (latticePhysicalPoint d N (L / (N : ℝ)) x)) ^ 2) := by
  have h := finiteFourier_norm_sq d N
    (fun x => (((L / (N : ℝ)) ^ d * f (latticePhysicalPoint d N (L / (N : ℝ)) x) : ℝ) : ℂ))
  simp_rw [finiteFourierCoefficient_physical_sample] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow] at h
  rw [← Finset.mul_sum] at h
  have hv : (N : ℝ) ^ d * (L / (N : ℝ)) ^ d = L ^ d := by
    rw [← mul_pow, mul_div_cancel₀ _ (by exact_mod_cast (NeZero.ne N))]
  rw [h]
  calc
    (N : ℝ) ^ d * (((L / (N : ℝ)) ^ d) ^ 2 *
      ∑ x : FinLatticeSites d N, (f (latticePhysicalPoint d N (L / (N : ℝ)) x)) ^ 2) =
      ((N : ℝ) ^ d * (L / (N : ℝ)) ^ d) * ((L / (N : ℝ)) ^ d *
        ∑ x : FinLatticeSites d N, (f (latticePhysicalPoint d N (L / (N : ℝ)) x)) ^ 2) := by ring
    _ = _ := by rw [hv]

/-- Uniform physical Fourier energy bound. Periodicity is unnecessary for this
finite estimate: bounded site samples alone suffice. -/
theorem sampledFourierCoefficient_norm_sq_sum_le
    (d N : ℕ) [NeZero N] (L : ℝ) (hL : 0 < L)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    (∑ p : FinLatticeSites d N, ‖sampledFourierCoefficient d N L f p‖ ^ 2) ≤
      L ^ (2 * d) * ‖f‖ ^ 2 := by
  rw [sampledFourierCoefficient_parseval]
  have ha : 0 < L / (N : ℝ) := div_pos hL (Nat.cast_pos.mpr (NeZero.pos N))
  have hs := sampled_testSeminormSq_le d N (L / (N : ℝ)) ha f
  rw [div_mul_cancel₀ _ (by exact_mod_cast (NeZero.ne N))] at hs
  have hm := mul_le_mul_of_nonneg_left hs (le_of_lt (pow_pos hL d))
  change L ^ d * ((L / (N : ℝ)) ^ d * ∑ x : FinLatticeSites d N,
    (f (latticePhysicalPoint d N (L / (N : ℝ)) x)) ^ 2) ≤ _ at hm
  convert hm using 1 <;> ring

/-- Signed integer frequencies in the symmetric box `[-K,K]^d`, represented by
`Fin (2*K+1)^d`. This is the same index set used by the existing cutoff. -/
def torusIntegerFrequencyMode (d K : ℕ)
    (q : Fin d → Fin (2 * K + 1)) : Fin d → ℤ :=
  fun i => (q i).val - (K : ℤ)

/-- The finite symmetric integer frequency box. -/
def torusIntegerFrequencyBox (d K : ℕ) : Finset (Fin d → ℤ) :=
  Finset.univ.image (torusIntegerFrequencyMode d K)

theorem torusIntegerFrequencyMode_injective (d K : ℕ) :
    Function.Injective (torusIntegerFrequencyMode d K) := by
  intro q r h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  dsimp [torusIntegerFrequencyMode] at hi
  omega

theorem torusIntegerFrequencyBox_mem_iff (d K : ℕ) (k : Fin d → ℤ) :
    k ∈ torusIntegerFrequencyBox d K ↔
      ∀ i, -(K : ℤ) ≤ k i ∧ k i ≤ (K : ℤ) := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨q, hq, hmode⟩
    rw [← hmode]
    intro i
    constructor <;> dsimp [torusIntegerFrequencyMode] <;> omega
  · intro hk
    let q : Fin d → Fin (2 * K + 1) := fun i =>
      ⟨(k i + (K : ℤ)).toNat, by
        have hcast : (((k i + (K : ℤ)).toNat : ℕ) : ℤ) = k i + K :=
          Int.toNat_of_nonneg (by have := (hk i).1; omega)
        have hu := (hk i).2
        omega⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_univ _, ?_⟩
    funext i
    dsimp [torusIntegerFrequencyMode, q]
    have hcast : (((k i + (K : ℤ)).toNat : ℕ) : ℤ) = k i + K :=
      Int.toNat_of_nonneg (by have := (hk i).1; omega)
    omega

theorem torusIntegerFrequencyBox_mono (d : ℕ) :
    Monotone (torusIntegerFrequencyBox d) := by
  intro K J hKJ k hk
  rw [torusIntegerFrequencyBox_mem_iff] at hk ⊢
  intro i
  rcases hk i with ⟨hlo, hhi⟩
  constructor <;> omega

def torusIntegerFrequencyRadius (d : ℕ) (k : Fin d → ℤ) : ℕ :=
  Finset.univ.sup fun i => (k i).natAbs

theorem torusIntegerFrequencyBox_cover (d : ℕ) (k : Fin d → ℤ) :
    ∃ K, k ∈ torusIntegerFrequencyBox d K := by
  refine ⟨torusIntegerFrequencyRadius d k, ?_⟩
  rw [torusIntegerFrequencyBox_mem_iff]
  intro i
  have hn : (k i).natAbs ≤ torusIntegerFrequencyRadius d k :=
    Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ i)
  have hc : ((k i).natAbs : ℤ) ≤ (torusIntegerFrequencyRadius d k : ℤ) := by
    exact_mod_cast hn
  have ha : |k i| ≤ (torusIntegerFrequencyRadius d k : ℤ) := by
    simpa only [Int.abs_eq_natAbs] using hc
  exact abs_le.mp ha

theorem torusIntegerFrequencyBox_tendsto (d : ℕ) :
    Filter.Tendsto (torusIntegerFrequencyBox d) Filter.atTop Filter.atTop :=
  (torusIntegerFrequencyBox_mono d).tendsto_atTop_finset
    (torusIntegerFrequencyBox_cover d)

theorem torusIntegerFrequencyBox_sum_eq (d K : ℕ) (F : (Fin d → ℤ) → ℝ) :
    (∑ k ∈ torusIntegerFrequencyBox d K, F k) =
      ∑ q : Fin d → Fin (2 * K + 1), F (torusIntegerFrequencyMode d K q) := by
  classical
  unfold torusIntegerFrequencyBox
  rw [Finset.sum_image]
  intro q hq r hr h
  exact torusIntegerFrequencyMode_injective d K h

set_option maxHeartbeats 1000000 in
/-- Finite-box Bessel bound obtained as the limit of the discrete Parseval
bound, using the already-proved fixed-mode coefficient convergence. -/
theorem torusFourierCoefficient_norm_sq_box_sum_le
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) :
    (∑ q : Fin d → Fin (2 * K + 1),
      ‖torusFourierCoefficient d L f (torusIntegerFrequencyMode d K q)‖ ^ 2) ≤
      L ^ (2 * d) * ‖f‖ ^ 2 := by
  let C : ℝ := L ^ (2 * d) * ‖f‖ ^ 2
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      (∑ q : Fin d → Fin (2 * K + 1),
        ‖sampledFourierCoefficient d (n + 1) L f
          (integerLatticeMode d (n + 1) (torusIntegerFrequencyMode d K q))‖ ^ 2) ≤ C := by
    filter_upwards [Filter.eventually_ge_atTop (2 * K)] with n hn
    let N := n + 1
    letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    have hN : 2 * K < N := by dsimp [N]; omega
    have hparseval := sampledFourierCoefficient_norm_sq_sum_le d N L hL f
    classical
    let e : (Fin d → Fin (2 * K + 1)) → FinLatticeSites d N :=
      fun q => integerLatticeMode d N (torusIntegerFrequencyMode d K q)
    have he : Function.Injective e := by
      intro q r h
      funext i
      apply frequencyBoxMode_injective N K hN
      exact congrFun h i
    have hsub : (∑ q : Fin d → Fin (2 * K + 1),
        ‖sampledFourierCoefficient d N L f (e q)‖ ^ 2) ≤
        ∑ p : FinLatticeSites d N, ‖sampledFourierCoefficient d N L f p‖ ^ 2 := by
      apply Finset.sum_le_sum_of_injOn e
        (fun _ _ _ _ h => he h) (Finset.subset_univ _)
      · intro q hq
        exact le_rfl
      · intro p hp hnot
        exact sq_nonneg _
    exact hsub.trans hparseval
  have hterm (q : Fin d → Fin (2 * K + 1)) :
      Filter.Tendsto
        (fun n : ℕ =>
          ‖sampledFourierCoefficient d (n + 1) L f
            (integerLatticeMode d (n + 1) (torusIntegerFrequencyMode d K q))‖ ^ 2)
        Filter.atTop
        (nhds (‖torusFourierCoefficient d L f (torusIntegerFrequencyMode d K q)‖ ^ 2)) := by
    have hc := sampledFourierCoefficient_integerLatticeMode_tendsto d L hL f
      (torusIntegerFrequencyMode d K q)
    have hn := (continuous_norm.continuousAt).tendsto.comp hc
    exact hn.pow 2
  have hsum := tendsto_finsetSum Finset.univ (fun q _ => hterm q)
  have hlim : Filter.Tendsto
      (fun n : ℕ =>
        ∑ q : Fin d → Fin (2 * K + 1),
          ‖sampledFourierCoefficient d (n + 1) L f
            (integerLatticeMode d (n + 1) (torusIntegerFrequencyMode d K q))‖ ^ 2)
      Filter.atTop
      (nhds (∑ q : Fin d → Fin (2 * K + 1),
        ‖torusFourierCoefficient d L f (torusIntegerFrequencyMode d K q)‖ ^ 2)) := by
    simpa using hsum
  have hle := le_of_tendsto_of_tendsto hlim tendsto_const_nhds hbound
  simpa [C] using hle


theorem torusIntegerFrequencyBox_complex_sum_eq (d K : ℕ) (F : (Fin d → ℤ) → ℂ) :
    (∑ k ∈ torusIntegerFrequencyBox d K, F k) =
      ∑ q : Fin d → Fin (2 * K + 1), F (torusIntegerFrequencyMode d K q) := by
  classical
  unfold torusIntegerFrequencyBox
  rw [Finset.sum_image]
  intro q hq r hr h
  exact torusIntegerFrequencyMode_injective d K h

/-- Finite Parseval bounds pass to the continuum and exhaust all lattice
frequencies; no Fourier completeness or assumed Bessel inequality is used. -/
theorem torusFourierCoefficient_norm_sq_summable
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (f : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Summable (fun k : Fin d → ℤ => ‖torusFourierCoefficient d L f k‖ ^ 2) := by
  apply summable_of_sum_le (fun k => sq_nonneg ‖torusFourierCoefficient d L f k‖)
  intro s
  have hcofinal : ∃ K, s ⊆ torusIntegerFrequencyBox d K := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | @insert a s ha ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨J, hJ⟩ := torusIntegerFrequencyBox_cover d a
      refine ⟨max J K, Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
      · exact torusIntegerFrequencyBox_mono d (le_max_left J K) hJ
      · exact hK.trans (torusIntegerFrequencyBox_mono d (le_max_right J K))
  obtain ⟨K, hK⟩ := hcofinal
  calc
    (∑ k ∈ s, ‖torusFourierCoefficient d L f k‖ ^ 2) ≤
        ∑ k ∈ torusIntegerFrequencyBox d K, ‖torusFourierCoefficient d L f k‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hK (by intros; positivity)
    _ = ∑ q : Fin d → Fin (2 * K + 1),
        ‖torusFourierCoefficient d L f (torusIntegerFrequencyMode d K q)‖ ^ 2 :=
      torusIntegerFrequencyBox_sum_eq d K _
    _ ≤ L ^ (2 * d) * ‖f‖ ^ 2 := torusFourierCoefficient_norm_sq_box_sum_le d L hL f K

/-- The continuous Green series is absolutely summable. A Young bound by the
two coefficient-energy sequences avoids any extra regularity assumption. -/
theorem torusFourierGreenTerm_norm_summable
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Summable (fun k : Fin d → ℤ =>
      ‖star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
        (torusMassSymbol d L mass k : ℂ)‖) := by
  let F : (Fin d → ℤ) → ℂ := fun k =>
    star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
      (torusMassSymbol d L mass k : ℂ)
  let G : (Fin d → ℤ) → ℝ := fun k =>
    (‖torusFourierCoefficient d L f k‖ ^ 2 +
      ‖torusFourierCoefficient d L g k‖ ^ 2) / mass ^ 2
  have hf := torusFourierCoefficient_norm_sq_summable d L hL f
  have hg := torusFourierCoefficient_norm_sq_summable d L hL g
  have hG : Summable G := by
    simpa only [G] using (hf.add hg).div_const (mass ^ 2)
  have hbound (k : Fin d → ℤ) : ‖F k‖ ≤ G k := by
    dsimp [F, G]
    have hDpos := torusMassSymbol_pos d L mass hmass k
    have hDge : mass ^ 2 ≤ torusMassSymbol d L mass k := by
      unfold torusMassSymbol
      apply le_add_of_nonneg_right
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hDnorm : ‖(torusMassSymbol d L mass k : ℂ)‖ = torusMassSymbol d L mass k :=
      Complex.norm_of_nonneg hDpos.le
    have hprod :
        ‖torusFourierCoefficient d L f k‖ * ‖torusFourierCoefficient d L g k‖ ≤
          ‖torusFourierCoefficient d L f k‖ ^ 2 +
            ‖torusFourierCoefficient d L g k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖torusFourierCoefficient d L f k‖ -
        ‖torusFourierCoefficient d L g k‖)]
    rw [norm_div, norm_mul]
    simp only [Complex.star_def, Complex.norm_conj, hDnorm]
    calc
      ‖torusFourierCoefficient d L f k‖ * ‖torusFourierCoefficient d L g k‖ /
          torusMassSymbol d L mass k ≤
        (‖torusFourierCoefficient d L f k‖ ^ 2 +
          ‖torusFourierCoefficient d L g k‖ ^ 2) / torusMassSymbol d L mass k :=
        div_le_div_of_nonneg_right hprod hDpos.le
      _ ≤ (‖torusFourierCoefficient d L f k‖ ^ 2 +
          ‖torusFourierCoefficient d L g k‖ ^ 2) / mass ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hmass) hDge
  exact hG.of_nonneg_of_le (fun _ => norm_nonneg _) hbound

/-- Each massive Fourier square term has nonnegative real part. -/
theorem torusFourierSquareTerm_re_nonneg
    (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (k : Fin d → ℤ) (z : ℂ) :
    0 ≤ (star z * z / (torusMassSymbol d L mass k : ℂ)).re := by
  have hD := torusMassSymbol_pos d L mass hmass k
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_div, mul_zero, add_zero]
  simp [Complex.normSq]
  exact div_nonneg
    (mul_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) hD.le)
    (mul_nonneg hD.le hD.le)

/-- At each frequency, a finite real quadratic combination is a weighted complex square. -/
theorem torusFourierGreenTerm_quadratic_eq_square
    (d m : ℕ) (L mass : ℝ) (t : Fin m → ℝ)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (k : Fin d → ℤ) :
    (∑ i : Fin m, ∑ j : Fin m,
      (t i : ℂ) * (t j : ℂ) *
        (star (torusFourierCoefficient d L (fs i) k) *
          torusFourierCoefficient d L (fs j) k /
          (torusMassSymbol d L mass k : ℂ))) =
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ) := by
  simp [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, Complex.star_def, Complex.conj_ofReal]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The complete Fourier Green pairing is symmetric by negative-frequency reindexing. -/
theorem torusFourierGreenPairing_symm
    (d : ℕ) (L mass : ℝ)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    torusFourierGreenPairing d L mass f g =
      torusFourierGreenPairing d L mass g f := by
  unfold torusFourierGreenPairing
  congr 1
  rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq]
  congr 1
  funext k
  simp only [Equiv.neg_apply]
  rw [torusFourierCoefficient_star_eq_neg,
    torusFourierCoefficient_star_eq_neg]
  have hmassneg : torusMassSymbol d L mass (-k) = torusMassSymbol d L mass k := by
    simp [torusMassSymbol]
  rw [hmassneg, neg_neg, mul_comm]

theorem torusFourierGreenTerm_summable
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Summable (fun k : Fin d → ℤ =>
      star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
        (torusMassSymbol d L mass k : ℂ)) :=
  (torusFourierGreenTerm_norm_summable d L mass hL hmass f g).of_norm

/-- The finite quadratic Green-term sum is summable, by two finite-sum inductions. -/
lemma torusFourierGreenTerm_quadratic_summable
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (t : Fin m → ℝ)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Summable (fun k : Fin d → ℤ =>
      ∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) *
          (star (torusFourierCoefficient d L (fs i) k) *
            torusFourierCoefficient d L (fs j) k /
            (torusMassSymbol d L mass k : ℂ))) := by
  let Q : Fin m → Fin m → (Fin d → ℤ) → ℂ := fun i j k =>
    (t i : ℂ) * (t j : ℂ) *
      (star (torusFourierCoefficient d L (fs i) k) *
        torusFourierCoefficient d L (fs j) k /
        (torusMassSymbol d L mass k : ℂ))
  have hsingle (i j : Fin m) : Summable (Q i j) := by
    dsimp [Q]
    have h := torusFourierGreenTerm_summable d L mass hL hmass (fs i) (fs j)
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (h.mul_left (t i : ℂ)).mul_left (t j : ℂ)
  have hinner (i : Fin m) (s : Finset (Fin m)) :
      Summable (fun k => s.sum (fun j => Q i j k)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hsingle i j).add ih
  have houter (s : Finset (Fin m)) :
      Summable (fun k => s.sum (fun i => Finset.univ.sum (fun j => Q i j k))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hinner i Finset.univ).add ih
  simpa [Q] using houter (Finset.univ : Finset (Fin m))

/-- The real part of the summed Fourier square is nonnegative. -/
theorem torusFourierSquareTsum_re_nonneg
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (t : Fin m → ℝ)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    0 ≤ (∑' k : Fin d → ℤ,
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)).re := by
  have hq0 := torusFourierGreenTerm_quadratic_summable d m L mass hL hmass t fs
  have hq : Summable (fun k : Fin d → ℤ =>
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)) := by
    simpa only [torusFourierGreenTerm_quadratic_eq_square d m L mass t fs] using hq0
  rw [Complex.re_tsum hq]
  apply tsum_nonneg
  intro k
  exact torusFourierSquareTerm_re_nonneg d L mass hmass k _

/-- The positive real prefactor preserves the nonnegative Fourier square sum. -/
lemma torusFourierSquareTsum_prefactor_re_nonneg
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (t : Fin m → ℝ)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    0 ≤ ((L : ℂ)⁻¹ ^ d * ∑' k : Fin d → ℤ,
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)).re := by
  have hsum := torusFourierSquareTsum_re_nonneg d m L mass hL hmass t fs
  have hpref : (L : ℂ)⁻¹ ^ d = (L⁻¹ ^ d : ℝ) := by simp [Complex.ofReal_inv]
  rw [hpref, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) hsum

/-- The Fourier pairing quadratic form is exactly the prefactored square tsum. -/
lemma torusFourierGreenPairing_quadratic_eq_square_tsum
    (d m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (t : Fin m → ℝ)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ((L : ℂ)⁻¹ ^ d * ∑' k : Fin d → ℤ,
      star (∑ i : Fin m, (t i : ℂ) * torusFourierCoefficient d L (fs i) k) *
        (∑ j : Fin m, (t j : ℂ) * torusFourierCoefficient d L (fs j) k) /
          (torusMassSymbol d L mass k : ℂ)) =
      ∑ i : Fin m, ∑ j : Fin m,
        (t i : ℂ) * (t j : ℂ) * torusFourierGreenPairing d L mass (fs i) (fs j) := by
  let Q : Fin m → Fin m → (Fin d → ℤ) → ℂ := fun i j k =>
    (t i : ℂ) * (t j : ℂ) *
      (star (torusFourierCoefficient d L (fs i) k) *
        torusFourierCoefficient d L (fs j) k /
        (torusMassSymbol d L mass k : ℂ))
  have hsingle (i j : Fin m) : Summable (Q i j) := by
    dsimp [Q]
    have h := torusFourierGreenTerm_summable d L mass hL hmass (fs i) (fs j)
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (h.mul_left (t i : ℂ)).mul_left (t j : ℂ)
  have hinner (i : Fin m) (s : Finset (Fin m)) :
      Summable (fun k => s.sum (fun j => Q i j k)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hsingle i j).add ih
  have hq0 : Summable (fun k => Finset.univ.sum (fun i => Finset.univ.sum (fun j => Q i j k))) := by
    exact torusFourierGreenTerm_quadratic_summable d m L mass hL hmass t fs
  have hswapOuter :
      (∑' k, Finset.univ.sum (fun i => Finset.univ.sum (fun j => Q i j k))) =
        Finset.univ.sum (fun i => ∑' k, Finset.univ.sum (fun j => Q i j k)) := by
    apply Summable.tsum_finsetSum
    intro i hi
    exact hinner i Finset.univ
  have hswapInner (i : Fin m) :
      (∑' k, Finset.univ.sum (fun j => Q i j k)) =
        Finset.univ.sum (fun j => ∑' k, Q i j k) := by
    apply Summable.tsum_finsetSum
    intro j hj
    exact hsingle i j
  simp_rw [← torusFourierGreenTerm_quadratic_eq_square d m L mass t fs]
  change (L : ℂ)⁻¹ ^ d * (∑' k, Finset.univ.sum (fun i => Finset.univ.sum (fun j => Q i j k))) = _
  rw [hswapOuter]
  simp_rw [hswapInner]
  simp only [torusFourierGreenPairing, Q]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [← tsum_mul_left]
  ring_nf

/-- The existing `Fin (2*K+1)` cutoff is exactly the sum over the exhausting
integer box, so its limit follows from absolute summability. -/
theorem torusFourierGreenCutoff_eq_box_sum
    (d : ℕ) (L mass : ℝ)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) :
    torusFourierGreenCutoff d L mass f g K =
      (L : ℂ)⁻¹ ^ d *
        ∑ k ∈ torusIntegerFrequencyBox d K,
          star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
            (torusMassSymbol d L mass k : ℂ) := by
  let F : (Fin d → ℤ) → ℂ := fun k =>
    star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
      (torusMassSymbol d L mass k : ℂ)
  unfold torusFourierGreenCutoff
  change (L : ℂ)⁻¹ ^ d *
      ∑ q : Fin d → Fin (2 * K + 1), F (torusIntegerFrequencyMode d K q) =
    (L : ℂ)⁻¹ ^ d *
      ∑ k ∈ torusIntegerFrequencyBox d K, F k
  rw [← torusIntegerFrequencyBox_complex_sum_eq d K F]

theorem torusFourierGreenCutoff_tendsto
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Filter.Tendsto (fun K => torusFourierGreenCutoff d L mass f g K)
      Filter.atTop (nhds (torusFourierGreenPairing d L mass f g)) := by
  have hbox := torusIntegerFrequencyBox_tendsto d
  have hseries := (torusFourierGreenTerm_summable d L mass hL hmass f g).hasSum.comp hbox
  have hscaled := hseries.const_mul ((L : ℂ)⁻¹ ^ d)
  simpa only [torusFourierGreenCutoff_eq_box_sum, torusFourierGreenPairing, Function.comp_def] using hscaled

theorem torusFourierGreenCutoff_re_tendsto
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Filter.Tendsto (fun K => (torusFourierGreenCutoff d L mass f g K).re)
      Filter.atTop (nhds (torusFourierGreenPairing d L mass f g).re) :=
  Complex.continuous_re.continuousAt.tendsto.comp
    (torusFourierGreenCutoff_tendsto d L mass hL hmass f g)

theorem torusFourierGreenCutoff_error_norm_tendsto_zero
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Filter.Tendsto
      (fun K => ‖torusFourierGreenPairing d L mass f g -
        torusFourierGreenCutoff d L mass f g K‖)
      Filter.atTop (nhds 0) := by
  have hconst : Filter.Tendsto
      (fun _ : ℕ => torusFourierGreenPairing d L mass f g)
      Filter.atTop (nhds (torusFourierGreenPairing d L mass f g)) := tendsto_const_nhds
  have htail : Filter.Tendsto
      (fun K : ℕ => torusFourierGreenPairing d L mass f g -
        torusFourierGreenCutoff d L mass f g K)
      Filter.atTop (nhds (0 : ℂ)) := by
    simpa using hconst.sub
      (torusFourierGreenCutoff_tendsto d L mass hL hmass f g)
  have hn := (continuous_norm.continuousAt).tendsto.comp htail
  simpa only [Function.comp_def, norm_zero] using hn

/-- Every fixed cutoff converges as a complex pairing to its continuous
integer box pairing, using exact reindexing once N exceeds twice K. -/
theorem discreteFourierGreenCutoff_tendsto
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) :
    Filter.Tendsto (fun n : ℕ => discreteFourierGreenCutoff d (n + 1) L mass f g K)
      Filter.atTop (nhds (torusFourierGreenCutoff d L mass f g K)) := by
  have hterm (q : Fin d → Fin (2 * K + 1)) :=
    ((sampledFourierCoefficient_integerLatticeMode_tendsto d L hL f
      (fun i => (q i).val - (K : ℤ))).star.mul
      (sampledFourierCoefficient_integerLatticeMode_tendsto d L hL g
      (fun i => (q i).val - (K : ℤ)))).mul
      (fixedVolumeMassSymbol_integerLatticeMode_inv_tendsto d L mass hmass
      (fun i => (q i).val - (K : ℤ)))
  have hsum := tendsto_finsetSum Finset.univ (fun q _ => hterm q)
  have hh := hsum.const_mul ((L : ℂ)⁻¹ ^ d)
  apply Filter.Tendsto.congr' _ (by
    simpa only [torusFourierGreenCutoff, div_eq_mul_inv] using hh)
  filter_upwards [Filter.eventually_ge_atTop (2 * K)] with n hn
  rw [discreteFourierGreenCutoff_eq_integer_box d (n + 1) L mass f g K (by omega)]
  simp only [div_eq_mul_inv]

/-- Real fixed-cutoff convergence in the form used by the analysis interface. -/
theorem discreteFourierGreenCutoff_re_tendsto
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) :
    Filter.Tendsto (fun n : ℕ => (discreteFourierGreenCutoff d (n + 1) L mass f g K).re)
      Filter.atTop (nhds (torusFourierGreenCutoff d L mass f g K).re) :=
  Complex.continuous_re.continuousAt.tendsto.comp
    (discreteFourierGreenCutoff_tendsto d L mass hL hmass f g K)

/-- The fixed-volume sequence of discrete GJ covariance inner products. The
physical period is `L`, the lattice size is `N = n + 1`, and the cell size is
`a = L / N`. Periodic lattice boundary conditions are carried by `ZMod N`. -/
def fixedVolumeCovarianceInner
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (n : ℕ) : ℝ :=
  let N := n + 1
  letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
  @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
    (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n)))
      hmass
      (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
    (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n)))
      hmass
      (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g))

/-- Cauchy-Schwarz in the physical Fourier normalization. -/
theorem sampledFourierCoefficient_norm_product_sum_le
    (d N : ℕ) [NeZero N] (L : ℝ) (hL : 0 < L)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    (∑ p : FinLatticeSites d N, ‖sampledFourierCoefficient d N L f p‖ *
      ‖sampledFourierCoefficient d N L g p‖) ≤ L ^ (2 * d) * ‖f‖ * ‖g‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : FinLatticeSites d N => ‖sampledFourierCoefficient d N L f p‖)
    (fun p : FinLatticeSites d N => ‖sampledFourierCoefficient d N L g p‖)
  have hf := sampledFourierCoefficient_norm_sq_sum_le d N L hL f
  have hg := sampledFourierCoefficient_norm_sq_sum_le d N L hL g
  have hfg := mul_le_mul hf hg
    (Finset.sum_nonneg (fun p _ => sq_nonneg _)) (by positivity)
  have hsq := hcs.trans hfg
  have heq : (L ^ (2 * d) * ‖f‖ ^ 2) * (L ^ (2 * d) * ‖g‖ ^ 2) =
      (L ^ (2 * d) * ‖f‖ * ‖g‖) ^ 2 := by ring
  rw [heq] at hsq
  have hnon : 0 ≤ L ^ (2 * d) * ‖f‖ * ‖g‖ := by positivity
  have hsum : 0 ≤ ∑ p : FinLatticeSites d N, ‖sampledFourierCoefficient d N L f p‖ *
      ‖sampledFourierCoefficient d N L g p‖ :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith

/-- Uniform complex-norm tail estimate for every lattice size. Neither a
regularity modulus nor a periodicity hypothesis is needed for this estimate. -/
theorem discreteFourierGreenPairing_sub_cutoff_norm_le
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (K : ℕ) :
    ‖discreteFourierGreenPairing d N L mass f g -
      discreteFourierGreenCutoff d N L mass f g K‖ ≤
      L ^ d * ‖f‖ * ‖g‖ / (mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2) := by
  let R : ℝ := mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  let t : FinLatticeSites d N → ℂ := fun p =>
    star (sampledFourierCoefficient d N L f p) * sampledFourierCoefficient d N L g p /
      fixedVolumeMassSymbol d N L mass p
  let b : FinLatticeSites d N → ℂ := fun p =>
    if (∀ i : Fin d, min (p i).val (N - (p i).val) ≤ K) then t p else 0
  have hterm (p : FinLatticeSites d N) :
      ‖t p - b p‖ ≤
        (‖sampledFourierCoefficient d N L f p‖ * ‖sampledFourierCoefficient d N L g p‖) / R := by
    by_cases hp : ∀ i : Fin d, min (p i).val (N - (p i).val) ≤ K
    · simp only [b, if_pos hp, sub_self, norm_zero]
      positivity
    · have hlower := fixedVolumeMassSymbolReal_ge_outside_cutoff d N L mass hL p K hp
      have hpos := fixedVolumeMassSymbolReal_pos d N L mass hmass p
      simp only [b, if_neg hp, sub_zero, t, norm_div, norm_mul, norm_star,
        fixedVolumeMassSymbol_eq_real, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hR hlower
  have hsum : ‖∑ p : FinLatticeSites d N, (t p - b p)‖ ≤
      (L ^ (2 * d) * ‖f‖ * ‖g‖) / R := by
    calc
      _ ≤ ∑ p : FinLatticeSites d N, ‖t p - b p‖ := norm_sum_le _ _
      _ ≤ ∑ p : FinLatticeSites d N,
          (‖sampledFourierCoefficient d N L f p‖ * ‖sampledFourierCoefficient d N L g p‖) / R :=
        Finset.sum_le_sum (fun p _ => hterm p)
      _ = (∑ p : FinLatticeSites d N,
          ‖sampledFourierCoefficient d N L f p‖ * ‖sampledFourierCoefficient d N L g p‖) / R := by
        rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right
        (sampledFourierCoefficient_norm_product_sum_le d N L hL f g) hR.le
  have hnorm : ‖(L : ℂ)⁻¹ ^ d‖ = L⁻¹ ^ d := by
    simp [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  change ‖(L : ℂ)⁻¹ ^ d * (∑ p, t p) - (L : ℂ)⁻¹ ^ d * (∑ p, b p)‖ ≤ _
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, hnorm]
  calc
    _ ≤ L⁻¹ ^ d * ((L ^ (2 * d) * ‖f‖ * ‖g‖) / R) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      dsimp [R]
      rw [show L ^ (2 * d) = L ^ d * L ^ d by rw [two_mul, pow_add]]
      have hcancel : L⁻¹ ^ d * L ^ d = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]
      calc
        _ = (L⁻¹ ^ d * L ^ d) * (L ^ d * ‖f‖ * ‖g‖ /
            (mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2)) := by ring
        _ = _ := by rw [hcancel, one_mul]

/-- Exact finite Fourier formula for the original numbered GJ covariance on
physically sampled tests. The caller supplies no diagonalization assumptions. -/
theorem numberedLatticeCovarianceGJ_physical_eq_fourier
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    @inner ℝ (EuclideanSpace ℝ (Fin (Fintype.card (FinLatticeSites d N)))) _
      (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
        (div_pos hL (Nat.cast_pos.mpr (NeZero.pos N))) hmass
        (latticeTestField (physicalTestEval d N (L / (N : ℝ))) f))
      (numberedLatticeCovarianceGJ d N (L / (N : ℝ)) mass
        (div_pos hL (Nat.cast_pos.mpr (NeZero.pos N))) hmass
        (latticeTestField (physicalTestEval d N (L / (N : ℝ))) g)) =
      (discreteFourierGreenPairing d N L mass f g).re := by
  unfold numberedLatticeCovarianceGJ
  rw [reindexCovariance_inner]
  have hsample (u : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
      (fun x => latticeTestField (physicalTestEval d N (L / (N : ℝ))) u
        ((Fintype.equivFin (FinLatticeSites d N)) x)) =
      (fun x => (L / (N : ℝ)) ^ d * u (latticePhysicalPoint d N (L / (N : ℝ)) x)) := by
    funext x
    simp [latticeTestField, physicalTestEval]
  rw [hsample f, hsample g, latticeCovarianceGJ_inner_eq_fourier]
  simp_rw [finiteFourierCoefficient_physical_sample]
  have hscale : ((((L / (N : ℝ)) ^ d : ℝ) : ℂ))⁻¹ * (N : ℂ)⁻¹ ^ d =
      (L : ℂ)⁻¹ ^ d := by
    push_cast
    rw [← inv_pow, ← mul_pow, ← mul_inv,
      div_mul_cancel₀ _ (by exact_mod_cast (NeZero.ne N))]
  let t : ℂ := ∑ p : FinLatticeSites d N,
    star (sampledFourierCoefficient d N L f p) *
      (sampledFourierCoefficient d N L g p / fixedVolumeMassSymbol d N L mass p)
  change ((L / (N : ℝ)) ^ d : ℝ)⁻¹ * ((N : ℂ)⁻¹ ^ d * t).re = _
  calc
    ((L / (N : ℝ)) ^ d : ℝ)⁻¹ * ((N : ℂ)⁻¹ ^ d * t).re =
      (((((L / (N : ℝ)) ^ d : ℝ)⁻¹ : ℝ) : ℂ) * ((N : ℂ)⁻¹ ^ d * t)).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = ((L : ℂ)⁻¹ ^ d * t).re := by
      rw [Complex.ofReal_inv, ← mul_assoc, hscale]
    _ = (discreteFourierGreenPairing d N L mass f g).re := by
      congr 1
      unfold discreteFourierGreenPairing t
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- The actual fixed-volume covariance sequence equals its explicit finite
Fourier Green pairing, unconditionally at every lattice size. -/
theorem fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (n : ℕ) :
    fixedVolumeCovarianceInner d L mass hL hmass f g n =
      (discreteFourierGreenPairing d (n + 1) L mass f g).re := by
  exact numberedLatticeCovarianceGJ_physical_eq_fourier d (n + 1) L mass hL hmass f g

/-- The explicit tail majorant tends uniformly to zero. This elementary
Archimedean version supplies a single K0 for every lattice size. -/
theorem fixedVolume_tail_majorant_eventually_lt
    (L mass A : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀,
      A / (mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2) < ε := by
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (max 1 (A * L ^ 2 / (16 * ε)))
  refine ⟨K₀, ?_⟩
  intro K hK
  have hcast : (K₀ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hbig : A * L ^ 2 / (16 * ε) < (K : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) (hK₀.trans_le hcast)
  have hone : 1 ≤ (K : ℝ) :=
    (lt_of_le_of_lt (le_max_left _ _) (hK₀.trans_le hcast)).le
  have hbig' := (div_lt_iff₀ (show 0 < 16 * ε by positivity)).mp hbig
  have hR : 0 < mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2 := by positivity
  have hsq : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have hid : (mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2) * L ^ 2 =
      mass ^ 2 * L ^ 2 + 16 * (K : ℝ) ^ 2 := by
    field_simp
  have hlower : 16 * (K : ℝ) ≤
      (mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2) * L ^ 2 := by
    rw [hid]
    nlinarith [mul_nonneg (sq_nonneg mass) (sq_nonneg L)]
  have hm := mul_le_mul_of_nonneg_left hlower hε.le
  apply (div_lt_iff₀ hR).mpr
  apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos hL)).mp
  nlinarith only [hbig', hm]

/-- A single cutoff controls the complex Fourier tail at every N. -/
theorem discreteFourierGreenPairing_uniform_tail
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ (N : ℕ) [NeZero N],
      ‖discreteFourierGreenPairing d N L mass f g -
        discreteFourierGreenCutoff d N L mass f g K‖ < ε := by
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := fixedVolume_tail_majorant_eventually_lt L mass
    (L ^ d * ‖f‖ * ‖g‖) hL hmass ε hε
  refine ⟨K₀, ?_⟩
  intro K hK N inst
  exact lt_of_le_of_lt
    (discreteFourierGreenPairing_sub_cutoff_norm_le d N L mass hL hmass f g K) (hK₀ K hK)

/-- Actual GJ covariance inherits the explicit cutoff tail with its physical
normalization. -/
theorem fixedVolumeCovarianceInner_sub_cutoff_abs_le
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) (n K : ℕ) :
    |fixedVolumeCovarianceInner d L mass hL hmass f g n -
      (discreteFourierGreenCutoff d (n + 1) L mass f g K).re| ≤
      L ^ d * ‖f‖ * ‖g‖ / (mass ^ 2 + 16 * (K : ℝ) ^ 2 / L ^ 2) := by
  rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
  exact (Complex.abs_re_le_norm _).trans
    (discreteFourierGreenPairing_sub_cutoff_norm_le d (n + 1) L mass hL hmass f g K)

/-- The analysis interface's uniform-tail obligation is an unconditional finite
theorem for the actual covariance sequence. -/
theorem fixedVolumeCovarianceInner_uniform_tail
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ n : ℕ,
      |fixedVolumeCovarianceInner d L mass hL hmass f g n -
        (discreteFourierGreenCutoff d (n + 1) L mass f g K).re| < ε := by
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := fixedVolume_tail_majorant_eventually_lt L mass
    (L ^ d * ‖f‖ * ‖g‖) hL hmass ε hε
  refine ⟨K₀, ?_⟩
  intro K hK n
  exact lt_of_le_of_lt
    (fixedVolumeCovarianceInner_sub_cutoff_abs_le d L mass hL hmass f g n K) (hK₀ K hK)

/-- The remaining interface binds concrete covariance and target sequences to the
Fourier formula. Finite-mode convergence, coefficient square-summability, Green
series absolute summability, both cutoff limits, and uniform lattice tails are
proved below or above as reusable theorems. The `target_green` field binds the
chosen target to the Fourier series. The concrete series-target instance is
constructed below; identifying an independently defined continuum resolvent
with this series remains a separate operator theorem. -/

structure FixedVolumeFourierInterface
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g)
    (target : ℝ) where
  full : ℕ → ℝ
  cutoff : ℕ → ℕ → ℝ
  partialLimit : ℕ → ℝ
  full_fourier : ∀ n, full n =
    (discreteFourierGreenPairing d (n + 1) L mass f g).re
  cutoff_fourier : ∀ n K, cutoff n K =
    (discreteFourierGreenCutoff d (n + 1) L mass f g K).re
  partial_fourier : ∀ K,
    partialLimit K = (torusFourierGreenCutoff d L mass f g K).re
  target_green : target = (torusFourierGreenPairing d L mass f g).re

theorem FixedVolumeFourierInterface.green_summable
    {d : ℕ} {L mass : ℝ} {hL : 0 < L} {hmass : 0 < mass}
    {f g : BoundedContinuousFunction (Fin d → ℝ) ℝ}
    {hf : IsFlatTorusPeriodic d L f} {hg : IsFlatTorusPeriodic d L g} {target : ℝ}
    (H : FixedVolumeFourierInterface d L mass hL hmass f g hf hg target) :
    Summable (fun k : Fin d → ℤ =>
      star (torusFourierCoefficient d L f k) * torusFourierCoefficient d L g k /
        (torusMassSymbol d L mass k : ℂ)) :=
  torusFourierGreenTerm_summable d L mass hL hmass f g

theorem FixedVolumeFourierInterface.continuum_cutoff_tendsto
    {d : ℕ} {L mass : ℝ} {hL : 0 < L} {hmass : 0 < mass}
    {f g : BoundedContinuousFunction (Fin d → ℝ) ℝ}
    {hf : IsFlatTorusPeriodic d L f} {hg : IsFlatTorusPeriodic d L g} {target : ℝ}
    (H : FixedVolumeFourierInterface d L mass hL hmass f g hf hg target) :
    Filter.Tendsto H.partialLimit Filter.atTop (nhds target) := by
  have hpartial : H.partialLimit = fun K =>
      (torusFourierGreenCutoff d L mass f g K).re :=
    funext fun K => H.partial_fourier K
  rw [hpartial, H.target_green]
  exact torusFourierGreenCutoff_re_tendsto d L mass hL hmass f g

/-- The finite covariance/Fourier identity is a theorem, not an interface
assumption. Preserve its accessor form for consumers of the analysis interface. -/
theorem FixedVolumeFourierInterface.full_eq
    {d : ℕ} {L mass : ℝ} {hL : 0 < L} {hmass : 0 < mass}
    {f g : BoundedContinuousFunction (Fin d → ℝ) ℝ}
    {hf : IsFlatTorusPeriodic d L f} {hg : IsFlatTorusPeriodic d L g} {target : ℝ}
    (H : FixedVolumeFourierInterface d L mass hL hmass f g hf hg target) (n : ℕ) :
    fixedVolumeCovarianceInner d L mass hL hmass f g n = H.full n := by
  rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing, H.full_fourier]

/-- Uniform tails are derived from the finite estimates and no longer an
analysis-interface input. -/
theorem FixedVolumeFourierInterface.uniform_tail
    {d : ℕ} {L mass : ℝ} {hL : 0 < L} {hmass : 0 < mass}
    {f g : BoundedContinuousFunction (Fin d → ℝ) ℝ}
    {hf : IsFlatTorusPeriodic d L f} {hg : IsFlatTorusPeriodic d L g} {target : ℝ}
    (H : FixedVolumeFourierInterface d L mass hL hmass f g hf hg target) :
    ∀ ε > 0, ∃ K₀, ∀ K ≥ K₀, ∀ n, |H.full n - H.cutoff n K| < ε := by
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := fixedVolumeCovarianceInner_uniform_tail d L mass hL hmass f g ε hε
  refine ⟨K₀, ?_⟩
  intro K hK n
  rw [← H.full_eq n, H.cutoff_fourier]
  exact hK₀ K hK n

/-- Fixed-cutoff convergence is derived from physical Riemann sums and exact
frequency reindexing rather than supplied by the caller. -/
theorem FixedVolumeFourierInterface.mode_tendsto
    {d : ℕ} {L mass : ℝ} {hL : 0 < L} {hmass : 0 < mass}
    {f g : BoundedContinuousFunction (Fin d → ℝ) ℝ}
    {hf : IsFlatTorusPeriodic d L f} {hg : IsFlatTorusPeriodic d L g} {target : ℝ}
    (H : FixedVolumeFourierInterface d L mass hL hmass f g hf hg target) :
    ∀ K, Filter.Tendsto (fun n => H.cutoff n K) Filter.atTop (nhds (H.partialLimit K)) := by
  intro K
  simp_rw [H.cutoff_fourier, H.partial_fourier]
  exact discreteFourierGreenCutoff_re_tendsto d L mass hL hmass f g K

/-- The abstract cutoff lemma turns the explicit fixed-mode and tail inputs
into convergence of the exact discrete covariance inner product. -/
theorem fixedVolume_covariance_inner_tendsto_of_fourier_interface
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g)
    (target : ℝ) (H : FixedVolumeFourierInterface d L mass hL hmass f g hf hg target) :
    Filter.Tendsto (fixedVolumeCovarianceInner d L mass hL hmass f g)
      Filter.atTop (nhds target) := by
  rw [show fixedVolumeCovarianceInner d L mass hL hmass f g = H.full by
    funext n
    exact H.full_eq n]
  exact tendsto_of_cutoff_tail H.full H.cutoff
    H.partialLimit target H.mode_tendsto H.uniform_tail
    H.continuum_cutoff_tendsto

/-- Once the Fourier interface is instantiated for every pair of sampled test
functions, the actual pushed-forward GJ measures converge by the existing
exact covariance transfer theorem. -/
theorem physicalGJMeasure_fixedVolume_covariance_tendsto_of_fourier_interface
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (C : BoundedContinuousFunction (Fin d → ℝ) ℝ →
      BoundedContinuousFunction (Fin d → ℝ) ℝ → ℝ)
    (H : ∀ f g, ∀ hf : IsFlatTorusPeriodic d L f,
      ∀ hg : IsFlatTorusPeriodic d L g,
        FixedVolumeFourierInterface d L mass hL hmass f g hf hg (C f g)) :
    ∀ f g, ∀ hf : IsFlatTorusPeriodic d L f,
      ∀ hg : IsFlatTorusPeriodic d L g, Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          ω f * ω g ∂physicalGJMeasure d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass)
      Filter.atTop (nhds (C f g)) := by
  intro f g hf hg
  have hinner := fixedVolume_covariance_inner_tendsto_of_fourier_interface
    d L mass hL hmass f g hf hg (C f g) (H f g hf hg)
  have hEq (n : ℕ) :
      (let N := n + 1
       letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
       ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
         ω f * ω g ∂physicalGJMeasure d N (L / (N : ℝ)) mass
           (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass) =
      fixedVolumeCovarianceInner d L mass hL hmass f g n := by
    let N := n + 1
    letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
    exact physicalGJMeasure_mixedMoment d N (L / (N : ℝ)) mass
      (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass f g
  apply hinner.congr'
  filter_upwards [] with n
  exact (hEq n).symm

/-- The concrete Fourier-series target requires no extra analytic input.
Every convergence and tail property of this instance is supplied by the proved
interface accessors. This does not identify an independent continuum operator. -/
def fixedVolumeFourierSeriesInterface
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g) :
    FixedVolumeFourierInterface d L mass hL hmass f g hf hg
      (torusFourierGreenPairing d L mass f g).re where
  full n := (discreteFourierGreenPairing d (n + 1) L mass f g).re
  cutoff n K := (discreteFourierGreenCutoff d (n + 1) L mass f g K).re
  partialLimit K := (torusFourierGreenCutoff d L mass f g K).re
  full_fourier _ := rfl
  cutoff_fourier _ _ := rfl
  partial_fourier _ := rfl
  target_green := rfl

/-- Actual fixed-volume lattice covariance, with N = n+1 and a = L/N,
converges to the absolutely convergent continuum Fourier Green series. -/
theorem fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g) :
    Filter.Tendsto (fixedVolumeCovarianceInner d L mass hL hmass f g)
      Filter.atTop (nhds (torusFourierGreenPairing d L mass f g).re) :=
  fixedVolume_covariance_inner_tendsto_of_fourier_interface
    d L mass hL hmass f g hf hg _
    (fixedVolumeFourierSeriesInterface d L mass hL hmass f g hf hg)

/-- The mixed second moment of the actual pushed-forward physical GJ measures
converges to the continuum Fourier series, with no caller-supplied interface. -/
theorem physicalGJMeasure_fixedVolume_mixedMoment_tendsto_torusFourierGreenPairing
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g) :
    Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          ω f * ω g ∂physicalGJMeasure d N (L / (N : ℝ)) mass
            (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass)
      Filter.atTop (nhds (torusFourierGreenPairing d L mass f g).re) :=
  physicalGJMeasure_fixedVolume_covariance_tendsto_of_fourier_interface
    d L mass hL hmass (fun f g => (torusFourierGreenPairing d L mass f g).re)
    (fun f g hf hg => fixedVolumeFourierSeriesInterface d L mass hL hmass f g hf hg)
    f g hf hg

/-- The centered covariance has the same limit: both physical GJ test means
are exactly zero at every mesh size. No continuum resolvent identification is used. -/
theorem physicalGJMeasure_fixedVolume_covariance_tendsto_torusFourierGreenPairing
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g) :
    Filter.Tendsto
      (fun n : ℕ =>
        let N := n + 1
        letI : NeZero N := ⟨Nat.succ_ne_zero n⟩
        let μ := physicalGJMeasure d N (L / (N : ℝ)) mass
          (div_pos hL (Nat.cast_pos.mpr (Nat.succ_pos n))) hmass
        ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
          (ω f - ∫ η, η f ∂μ) * (ω g - ∫ η, η g ∂μ) ∂μ)
      Filter.atTop (nhds (torusFourierGreenPairing d L mass f g).re) := by
  have h := physicalGJMeasure_fixedVolume_mixedMoment_tendsto_torusFourierGreenPairing
    d L mass hL hmass f g hf hg
  apply h.congr'
  filter_upwards [] with n
  dsimp only
  rw [physicalGJMeasure_eval_mean_zero, physicalGJMeasure_eval_mean_zero]
  simp only [sub_zero]

end Pphi2Clean.Continuum
