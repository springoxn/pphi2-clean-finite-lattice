import AImathPPhi2Clean.RealFourierTestFunctions
import AImathPPhi2Clean.PeriodicFourierCovarianceLimit
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
open Pphi2Clean.UpstreamLattice
@[simp] theorem periodicCosineTest_norm_le_one (d : ℕ) (L : ℝ)
    (k : Fin d → ℤ) (hL : 0 < L) :
    ‖periodicCosineTest d L k hL‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num)]
  intro x
  rw [Real.norm_eq_abs]
  exact Real.abs_cos_le_one _
@[simp] theorem periodicSineTest_norm_le_one (d : ℕ) (L : ℝ)
    (k : Fin d → ℤ) (hL : 0 < L) :
    ‖periodicSineTest d L k hL‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num)]
  intro x
  rw [Real.norm_eq_abs]
  exact Real.abs_sin_le_one _
theorem physicalGJMeasure_periodicCosineTest_second_moment_le
    (d N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (k : Fin d → ℤ) (hperiod : 0 < L) :
    ∫ ω, (ω (periodicCosineTest d L k hperiod)) ^ 2 ∂
      physicalGJMeasure d N a mass ha hmass ≤ mass⁻¹ ^ 2 * L ^ d := by
  have h := physicalGJMeasure_fixed_volume_second_moment_le d N a mass L ha hmass hL
    (periodicCosineTest d L k hperiod)
  have hn := periodicCosineTest_norm_le_one d L k hperiod
  have hc : 0 ≤ mass⁻¹ ^ 2 * L ^ d := by positivity
  calc
    _ ≤ mass⁻¹ ^ 2 * L ^ d * ‖periodicCosineTest d L k hperiod‖ ^ 2 := h
    _ ≤ mass⁻¹ ^ 2 * L ^ d * 1 ^ 2 := by gcongr
    _ = mass⁻¹ ^ 2 * L ^ d := by ring
theorem physicalGJMeasure_periodicSineTest_second_moment_le
    (d N : ℕ) [NeZero N] (a mass L : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hL : a * (N : ℝ) = L) (k : Fin d → ℤ) (hperiod : 0 < L) :
    ∫ ω, (ω (periodicSineTest d L k hperiod)) ^ 2 ∂
      physicalGJMeasure d N a mass ha hmass ≤ mass⁻¹ ^ 2 * L ^ d := by
  have h := physicalGJMeasure_fixed_volume_second_moment_le d N a mass L ha hmass hL
    (periodicSineTest d L k hperiod)
  have hn := periodicSineTest_norm_le_one d L k hperiod
  have hc : 0 ≤ mass⁻¹ ^ 2 * L ^ d := by positivity
  calc
    _ ≤ mass⁻¹ ^ 2 * L ^ d * ‖periodicSineTest d L k hperiod‖ ^ 2 := h
    _ ≤ mass⁻¹ ^ 2 * L ^ d * 1 ^ 2 := by gcongr
    _ = mass⁻¹ ^ 2 * L ^ d := by ring

/-- Integral-normalized Fourier coefficient of a sampled periodic cosine test.
The two support terms are retained separately, so self-opposite residues are
counted with their correct merged multiplicity. -/
theorem sampledFourierCoefficient_periodicCosineTest
    (d N : ℕ) [NeZero N] (L : ℝ) (hL : 0 < L)
    (k : Fin d → ℤ) (p : FinLatticeSites d N) :
    sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p =
      ((if p = integerLatticeMode d N k then (L : ℂ)^d else 0) +
        (if p = -integerLatticeMode d N k then (L : ℂ)^d else 0)) / 2 := by
  rw [sampledFourierCoefficient]
  have hs (x : FinLatticeSites d N) :
      (periodicCosineTest d L k hL (latticePhysicalPoint d N (L / (N : ℝ)) x) : ℂ) =
        (periodicFourierCharacter d N (integerLatticeMode d N k) x).re := by
    rw [periodicFourierCharacter_eq_torusFourierPhase d N L hL.ne' k x]
    unfold torusFourierPhase
    change (Real.cos ((2 * Real.pi / L) *
      ∑ i : Fin d, (k i : ℝ) * latticePhysicalPoint d N (L / (N : ℝ)) x i) : ℂ) =
      (Complex.exp ((↑((2 * Real.pi / L) *
      ∑ i : Fin d, (k i : ℝ) * latticePhysicalPoint d N (L / (N : ℝ)) x i) : ℂ) * Complex.I)).re
    rw [Complex.exp_ofReal_mul_I_re]
  have hcoeff :
      (∑ x : FinLatticeSites d N,
        (periodicCosineTest d L k hL (latticePhysicalPoint d N (L / (N : ℝ)) x) : ℂ) *
          periodicFourierCharacter d N (-p) x) =
      finiteFourierCoefficient d N
        (fun x => (periodicFourierCharacter d N (integerLatticeMode d N k) x).re) p := by
    unfold finiteFourierCoefficient
    apply Finset.sum_congr rfl
    intro x hx
    rw [hs]
  rw [hcoeff, finiteFourierCoefficient_character_re]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hmul : (L / (N : ℝ)) * (N : ℝ) = L := by field_simp
  have hscaleR : (L / (N : ℝ)) ^ d * (N : ℝ)^d = L ^ d := by
    rw [← mul_pow, hmul]
  have hscale : ((L / (N : ℝ) : ℂ) ^ d) * (N : ℂ)^d = (L : ℂ)^d := by
    exact_mod_cast hscaleR
  have hscaleif (b : Prop) [Decidable b] :
      (((L / (N : ℝ)) ^ d : ℝ) : ℂ) * (if b then (N : ℂ)^d else 0) =
        if b then (L : ℂ)^d else 0 := by
    by_cases hb : b
    · simp [hb]
      exact_mod_cast hscaleR
    · simp [hb]
  rw [← mul_div_assoc]
  rw [mul_add]
  rw [hscaleif, hscaleif]

theorem sampledFourierCoefficient_periodicSineTest (d N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (k : Fin d → ℤ) (p : FinLatticeSites d N) :
    sampledFourierCoefficient d N L (periodicSineTest d L k hL) p =
      ((if p = integerLatticeMode d N k then (L : ℂ)^d else 0) -
        (if p = -integerLatticeMode d N k then (L : ℂ)^d else 0)) / (2 * Complex.I) := by
  rw [sampledFourierCoefficient]
  have hs (x : FinLatticeSites d N) :
      (periodicSineTest d L k hL (latticePhysicalPoint d N (L / (N : ℝ)) x) : ℂ) =
        (periodicFourierCharacter d N (integerLatticeMode d N k) x).im := by
    rw [periodicFourierCharacter_eq_torusFourierPhase d N L hL.ne' k x]
    unfold torusFourierPhase
    change (Real.sin ((2 * Real.pi / L) *
      ∑ i : Fin d, (k i : ℝ) * latticePhysicalPoint d N (L / (N : ℝ)) x i) : ℂ) =
      (Complex.exp ((↑((2 * Real.pi / L) *
      ∑ i : Fin d, (k i : ℝ) * latticePhysicalPoint d N (L / (N : ℝ)) x i) : ℂ) * Complex.I)).im
    rw [Complex.exp_ofReal_mul_I_im]
  have hcoeff :
      (∑ x : FinLatticeSites d N,
        (periodicSineTest d L k hL (latticePhysicalPoint d N (L / (N : ℝ)) x) : ℂ) *
          periodicFourierCharacter d N (-p) x) =
      finiteFourierCoefficient d N
        (fun x => (periodicFourierCharacter d N (integerLatticeMode d N k) x).im) p := by
    unfold finiteFourierCoefficient
    apply Finset.sum_congr rfl
    intro x hx
    rw [hs]
  rw [hcoeff, finiteFourierCoefficient_character_im]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hmul : (L / (N : ℝ)) * (N : ℝ) = L := by field_simp
  have hscaleR : (L / (N : ℝ)) ^ d * (N : ℝ)^d = L ^ d := by
    rw [← mul_pow, hmul]
  have hscale : ((L / (N : ℝ) : ℂ) ^ d) * (N : ℂ)^d = (L : ℂ)^d := by
    exact_mod_cast hscaleR
  have hscaleif (b : Prop) [Decidable b] :
      (((L / (N : ℝ)) ^ d : ℝ) : ℂ) * (if b then (N : ℂ)^d else 0) =
        if b then (L : ℂ)^d else 0 := by
    by_cases hb : b
    · simp [hb]
      exact_mod_cast hscaleR
    · simp [hb]
  rw [← mul_div_assoc]
  rw [mul_sub]
  rw [hscaleif, hscaleif]
/-- Exact cosine-probe Green pairing, including zero and Nyquist modes. -/
theorem discreteFourierGreenPairing_periodicCosineTest
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k : Fin d → ℤ) :
    discreteFourierGreenPairing d N L mass
      (periodicCosineTest d L k hL) (periodicCosineTest d L k hL) =
      if integerLatticeMode d N k = -integerLatticeMode d N k then
        (L : ℂ)^d / fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k)
      else
        ((L : ℂ)^d / fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k)) / 2 := by
  classical
  let q := integerLatticeMode d N k
  let C : ℂ := (L : ℂ)^d
  have hcoef (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p =
        ((if p = q then C else 0) + (if p = -q then C else 0)) / 2 := by
    dsimp [q, C]
    exact sampledFourierCoefficient_periodicCosineTest d N L hL k p
  have hqne : fixedVolumeMassSymbol d N L mass q ≠ 0 := by
    rw [fixedVolumeMassSymbol_eq_real]
    exact_mod_cast (fixedVolumeMassSymbolReal_pos d N L mass hmass q).ne'
  have hCne : C ≠ 0 := by
    dsimp [C]
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hL.ne')
  by_cases hself : q = -q
  · have hterm (p : FinLatticeSites d N) :
      star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
        sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p /
          fixedVolumeMassSymbol d N L mass p =
      if p = q then C ^ 2 / fixedVolumeMassSymbol d N L mass q else 0 := by
      rw [hcoef p]
      by_cases hp : p = q
      · subst p
        simp only [if_pos rfl, if_pos hself]
        simp [C]
        <;> ring
      · have hpn : p ≠ -q := by
          intro h
          have hp' : p = q := h.trans hself.symm
          exact hp hp'
        simp [hp, hpn]
    unfold discreteFourierGreenPairing
    change (L : ℂ)⁻¹ ^ d *
      ∑ p : FinLatticeSites d N,
        (star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
          sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p /
            fixedVolumeMassSymbol d N L mass p) = _
    simp_rw [hterm]
    rw [if_pos hself]
    simp [q, C]
    field_simp [hqne, hCne]
  · have hterm (p : FinLatticeSites d N) :
      star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
        sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p /
          fixedVolumeMassSymbol d N L mass p =
      (if p = q then C ^ 2 / (4 * fixedVolumeMassSymbol d N L mass q) else 0) +
      (if p = -q then C ^ 2 / (4 * fixedVolumeMassSymbol d N L mass q) else 0) := by
      rw [hcoef p]
      by_cases hp : p = q
      · subst p
        have hqn : q ≠ -q := hself
        simp [hqn, C]
        <;> ring
      · by_cases hpn : p = -q
        · subst p
          have hsym := fixedVolumeMassSymbol_neg d N L mass q
          simp [hp, hsym, C]
          <;> ring
        · simp [hp, hpn]
    unfold discreteFourierGreenPairing
    change (L : ℂ)⁻¹ ^ d *
      ∑ p : FinLatticeSites d N,
        (star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
          sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p /
            fixedVolumeMassSymbol d N L mass p) = _
    simp_rw [hterm]
    rw [if_neg hself]
    simp [Finset.sum_add_distrib, q, C]
    field_simp [hqne, hCne]
    <;> ring

/-- Exact sine-probe Green pairing; self-opposite modes vanish. -/
theorem discreteFourierGreenPairing_periodicSineTest
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k : Fin d → ℤ) :
    discreteFourierGreenPairing d N L mass
      (periodicSineTest d L k hL) (periodicSineTest d L k hL) =
      if integerLatticeMode d N k = -integerLatticeMode d N k then 0 else
        ((L : ℂ)^d / fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k)) / 2 := by
  classical
  let q := integerLatticeMode d N k
  let C : ℂ := (L : ℂ)^d
  let I : ℂ := (2 * Complex.I)⁻¹
  have hself' : integerLatticeMode d N k = -integerLatticeMode d N k ↔ q = -q := by rfl
  have hcoef (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicSineTest d L k hL) p =
        ((if p = q then C else 0) - (if p = -q then C else 0)) * I := by
    dsimp [q, C, I]
    exact sampledFourierCoefficient_periodicSineTest d N L hL k p
  have hqne : fixedVolumeMassSymbol d N L mass q ≠ 0 := by
    rw [fixedVolumeMassSymbol_eq_real]
    exact_mod_cast (fixedVolumeMassSymbolReal_pos d N L mass hmass q).ne'
  have hCne : C ≠ 0 := by
    dsimp [C]
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hL.ne')
  by_cases hself : q = -q
  · rw [if_pos (hself'.2 hself)]
    have hterm (p : FinLatticeSites d N) :
      star (sampledFourierCoefficient d N L (periodicSineTest d L k hL) p) *
        sampledFourierCoefficient d N L (periodicSineTest d L k hL) p /
          fixedVolumeMassSymbol d N L mass p = 0 := by
      rw [hcoef p]
      have hzero : (if p = q then C else 0) - (if p = -q then C else 0) = 0 := by
        by_cases hp : p = q
        · subst p
          simp only [if_pos hself]
          simp
        · have hpn : p ≠ -q := by
            intro h
            have hp' : p = q := h.trans hself.symm
            exact hp hp'
          simp only [if_neg hp, if_neg hpn]
          norm_num
      simp [hzero]
    unfold discreteFourierGreenPairing
    simp_rw [hterm]
    simp
  · rw [if_neg (mt hself'.1 hself)]
    have hterm (p : FinLatticeSites d N) :
      star (sampledFourierCoefficient d N L (periodicSineTest d L k hL) p) *
        sampledFourierCoefficient d N L (periodicSineTest d L k hL) p /
          fixedVolumeMassSymbol d N L mass p =
      (if p = q then C ^ 2 / (4 * fixedVolumeMassSymbol d N L mass q) else 0) +
      (if p = -q then C ^ 2 / (4 * fixedVolumeMassSymbol d N L mass q) else 0) := by
      rw [hcoef p]
      by_cases hp : p = q
      · subst p
        have hqn : q ≠ -q := hself
        simp [hqn, C, I]
        field_simp
        norm_num [Complex.I_sq]
      · by_cases hpn : p = -q
        · subst p
          have hsym := fixedVolumeMassSymbol_neg d N L mass q
          simp [hp, hsym, C, I]
          field_simp
          norm_num [Complex.I_sq]
        · simp [hp, hpn]
    unfold discreteFourierGreenPairing
    change (L : ℂ)⁻¹ ^ d *
      ∑ p : FinLatticeSites d N,
        (star (sampledFourierCoefficient d N L (periodicSineTest d L k hL) p) *
          sampledFourierCoefficient d N L (periodicSineTest d L k hL) p /
            fixedVolumeMassSymbol d N L mass p) = _
    simp_rw [hterm]
    simp [Finset.sum_add_distrib, q, C]
    field_simp [hqne, hCne]
    <;> ring

/-- The same-mode cosine/sine Green pairing vanishes, including self-opposite modes. -/
theorem discreteFourierGreenPairing_periodicCosineSineTest_sameMode
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k : Fin d → ℤ) :
    discreteFourierGreenPairing d N L mass
      (periodicCosineTest d L k hL) (periodicSineTest d L k hL) = 0 := by
  classical
  let q := integerLatticeMode d N k
  let C : ℂ := (L : ℂ)^d
  have hc (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p =
        ((if p = q then C else 0) + (if p = -q then C else 0)) / 2 := by
    dsimp [q, C]
    exact sampledFourierCoefficient_periodicCosineTest d N L hL k p
  have hs (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicSineTest d L k hL) p =
        ((if p = q then C else 0) - (if p = -q then C else 0)) / (2 * Complex.I) := by
    dsimp [q, C]
    exact sampledFourierCoefficient_periodicSineTest d N L hL k p
  by_cases hself : q = -q
  · have hs0 (p : FinLatticeSites d N) :
        sampledFourierCoefficient d N L (periodicSineTest d L k hL) p = 0 := by
      rw [hs p]
      have hz : (if p = q then C else 0) - (if p = -q then C else 0) = 0 := by
        by_cases hp : p = q
        · subst p
          simp only [if_pos hself]
          simp
        · have hpn : p ≠ -q := by
            intro h
            exact hp (h.trans hself.symm)
          simp only [if_neg hp, if_neg hpn]
          norm_num
      simp [hz]
    unfold discreteFourierGreenPairing
    simp_rw [hs0]
    simp
  · have hterm (p : FinLatticeSites d N) :
      star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
        sampledFourierCoefficient d N L (periodicSineTest d L k hL) p /
          fixedVolumeMassSymbol d N L mass p =
      (if p = q then C ^ 2 / (4 * Complex.I * fixedVolumeMassSymbol d N L mass q) else 0) -
      (if p = -q then C ^ 2 / (4 * Complex.I * fixedVolumeMassSymbol d N L mass q) else 0) := by
      rw [hc p, hs p]
      by_cases hp : p = q
      · subst p
        have hqn : q ≠ -q := hself
        simp [hqn, C]
        <;> field_simp <;> ring
      · by_cases hpn : p = -q
        · subst p
          have hsym := fixedVolumeMassSymbol_neg d N L mass q
          simp [hp, hsym, C]
          <;> field_simp <;> ring
        · simp [hp, hpn]
    unfold discreteFourierGreenPairing
    change (L : ℂ)⁻¹ ^ d *
      ∑ p : FinLatticeSites d N,
        (star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
          sampledFourierCoefficient d N L (periodicSineTest d L k hL) p /
          fixedVolumeMassSymbol d N L mass p) = 0
    simp_rw [hterm]
    simp [Finset.sum_sub_distrib, q]

/-- Cosine/sine Green pairing vanishes when the two opposite-frequency supports are disjoint. -/
theorem discreteFourierGreenPairing_periodicCosineSineTest_disjoint
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin d → ℤ)
    (hqr : integerLatticeMode d N k ≠ integerLatticeMode d N l)
    (hqn : integerLatticeMode d N k ≠ -integerLatticeMode d N l)
    (hnr : -integerLatticeMode d N k ≠ integerLatticeMode d N l)
    (hnn : -integerLatticeMode d N k ≠ -integerLatticeMode d N l) :
    discreteFourierGreenPairing d N L mass
      (periodicCosineTest d L k hL) (periodicSineTest d L l hL) = 0 := by
  classical
  let q := integerLatticeMode d N k
  let r := integerLatticeMode d N l
  let C : ℂ := (L : ℂ)^d
  have hc (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p =
        ((if p = q then C else 0) + (if p = -q then C else 0)) / 2 := by
    dsimp [q, C]
    exact sampledFourierCoefficient_periodicCosineTest d N L hL k p
  have hs (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicSineTest d L l hL) p =
        ((if p = r then C else 0) - (if p = -r then C else 0)) / (2 * Complex.I) := by
    dsimp [r, C]
    exact sampledFourierCoefficient_periodicSineTest d N L hL l p
  have hterm (p : FinLatticeSites d N) :
      star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
        sampledFourierCoefficient d N L (periodicSineTest d L l hL) p /
          fixedVolumeMassSymbol d N L mass p = 0 := by
    rw [hc p, hs p]
    by_cases hpq : p = q
    · subst p
      have hqr' : q ≠ r := hqr
      have hqn' : q ≠ -r := hqn
      have hnegqr : -q ≠ r := hnr
      have hnegn : -q ≠ -r := hnn
      simp [hqr', hqn', hnegqr, hnegn]
    · by_cases hpnq : p = -q
      · subst p
        have hqr' : -q ≠ r := hnr
        have hqn' : -q ≠ -r := hnn
        have hqrr : q ≠ r := hqr
        have hqnn : q ≠ -r := hqn
        simp [hqr', hqn', hqrr, hqnn]
      · simp [hpq, hpnq]
  unfold discreteFourierGreenPairing
  simp_rw [hterm]
  simp

/-- Cosine/cosine Green pairing vanishes for pairwise disjoint opposite supports. -/
theorem discreteFourierGreenPairing_periodicCosineTest_disjoint
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin d → ℤ)
    (hqr : integerLatticeMode d N k ≠ integerLatticeMode d N l)
    (hqn : integerLatticeMode d N k ≠ -integerLatticeMode d N l)
    (hnr : -integerLatticeMode d N k ≠ integerLatticeMode d N l)
    (hnn : -integerLatticeMode d N k ≠ -integerLatticeMode d N l) :
    discreteFourierGreenPairing d N L mass
      (periodicCosineTest d L k hL) (periodicCosineTest d L l hL) = 0 := by
  classical
  let q := integerLatticeMode d N k
  let r := integerLatticeMode d N l
  let C : ℂ := (L : ℂ)^d
  have hqr' : q ≠ r := by simpa [q, r] using hqr
  have hqn' : q ≠ -r := by simpa [q, r] using hqn
  have hnr' : -q ≠ r := by simpa [q, r] using hnr
  have hnn' : -q ≠ -r := by simpa [q, r] using hnn
  have hc (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p =
        ((if p = q then C else 0) + (if p = -q then C else 0)) / 2 := by
    dsimp [q, C]
    exact sampledFourierCoefficient_periodicCosineTest d N L hL k p
  have hl (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicCosineTest d L l hL) p =
        ((if p = r then C else 0) + (if p = -r then C else 0)) / 2 := by
    dsimp [r, C]
    exact sampledFourierCoefficient_periodicCosineTest d N L hL l p
  have hterm (p : FinLatticeSites d N) :
      star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
        sampledFourierCoefficient d N L (periodicCosineTest d L l hL) p /
          fixedVolumeMassSymbol d N L mass p = 0 := by
    by_cases hpq : p = q
    · subst p
      have hsecond :
          sampledFourierCoefficient d N L (periodicCosineTest d L l hL) q = 0 := by
        rw [hl q]
        simp [hqr', hqn']
      rw [hsecond]
      simp
    · by_cases hpnq : p = -q
      · subst p
        have hsecond :
            sampledFourierCoefficient d N L (periodicCosineTest d L l hL) (-q) = 0 := by
          rw [hl (-q)]
          simp [hnr', hnn']
        rw [hsecond]
        simp
      · rw [hc p]
        simp [hpq, hpnq]
  unfold discreteFourierGreenPairing
  simp_rw [hterm]
  simp

/-- Sine/sine Green pairing vanishes for pairwise disjoint opposite supports. -/
theorem discreteFourierGreenPairing_periodicSineTest_disjoint
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin d → ℤ)
    (hqr : integerLatticeMode d N k ≠ integerLatticeMode d N l)
    (hqn : integerLatticeMode d N k ≠ -integerLatticeMode d N l)
    (hnr : -integerLatticeMode d N k ≠ integerLatticeMode d N l)
    (hnn : -integerLatticeMode d N k ≠ -integerLatticeMode d N l) :
    discreteFourierGreenPairing d N L mass
      (periodicSineTest d L k hL) (periodicSineTest d L l hL) = 0 := by
  classical
  let q := integerLatticeMode d N k
  let r := integerLatticeMode d N l
  let C : ℂ := (L : ℂ)^d
  have hqr' : q ≠ r := by simpa [q, r] using hqr
  have hqn' : q ≠ -r := by simpa [q, r] using hqn
  have hnr' : -q ≠ r := by simpa [q, r] using hnr
  have hnn' : -q ≠ -r := by simpa [q, r] using hnn
  have hc (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicSineTest d L k hL) p =
        ((if p = q then C else 0) - (if p = -q then C else 0)) / (2 * Complex.I) := by
    dsimp [q, C]
    exact sampledFourierCoefficient_periodicSineTest d N L hL k p
  have hl (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicSineTest d L l hL) p =
        ((if p = r then C else 0) - (if p = -r then C else 0)) / (2 * Complex.I) := by
    dsimp [r, C]
    exact sampledFourierCoefficient_periodicSineTest d N L hL l p
  have hterm (p : FinLatticeSites d N) :
      star (sampledFourierCoefficient d N L (periodicSineTest d L k hL) p) *
        sampledFourierCoefficient d N L (periodicSineTest d L l hL) p /
          fixedVolumeMassSymbol d N L mass p = 0 := by
    by_cases hpq : p = q
    · subst p
      have hsecond : sampledFourierCoefficient d N L (periodicSineTest d L l hL) q = 0 := by
        rw [hl q]
        simp [hqr', hqn']
      rw [hsecond]
      simp
    · by_cases hpnq : p = -q
      · subst p
        have hsecond : sampledFourierCoefficient d N L (periodicSineTest d L l hL) (-q) = 0 := by
          rw [hl (-q)]
          simp [hnr', hnn']
        rw [hsecond]
        simp
      · rw [hc p]
        simp [hpq, hpnq]
  unfold discreteFourierGreenPairing
  simp_rw [hterm]
  simp

/-- Cosine probes with the same residue have the diagonal Green pairing. -/
theorem discreteFourierGreenPairing_periodicCosineTest_sameResidue
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin d → ℤ)
    (hmode : integerLatticeMode d N k = integerLatticeMode d N l) :
    discreteFourierGreenPairing d N L mass
      (periodicCosineTest d L k hL) (periodicCosineTest d L l hL) =
    if integerLatticeMode d N k = -integerLatticeMode d N k then
      (L : ℂ)^d / fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k)
    else
      ((L : ℂ)^d / fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k)) / 2 := by
  classical
  have hcoef (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicCosineTest d L l hL) p =
      sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p := by
    rw [sampledFourierCoefficient_periodicCosineTest, sampledFourierCoefficient_periodicCosineTest]
    simp [hmode]
  unfold discreteFourierGreenPairing
  simp_rw [hcoef]
  exact discreteFourierGreenPairing_periodicCosineTest d N L mass hL hmass k

/-- Sine probes with the same residue have the diagonal Green pairing. -/
theorem discreteFourierGreenPairing_periodicSineTest_sameResidue
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin d → ℤ)
    (hmode : integerLatticeMode d N k = integerLatticeMode d N l) :
    discreteFourierGreenPairing d N L mass
      (periodicSineTest d L k hL) (periodicSineTest d L l hL) =
    if integerLatticeMode d N k = -integerLatticeMode d N k then 0 else
      ((L : ℂ)^d / fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k)) / 2 := by
  classical
  have hcoef (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicSineTest d L l hL) p =
      sampledFourierCoefficient d N L (periodicSineTest d L k hL) p := by
    rw [sampledFourierCoefficient_periodicSineTest, sampledFourierCoefficient_periodicSineTest]
    simp [hmode]
  unfold discreteFourierGreenPairing
  simp_rw [hcoef]
  exact discreteFourierGreenPairing_periodicSineTest d N L mass hL hmass k

/-- Opposite residues give the same cosine sampled coefficients. -/
theorem discreteFourierGreenPairing_periodicCosineTest_oppositeResidue
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin d → ℤ)
    (hmode : integerLatticeMode d N k = -integerLatticeMode d N l) :
    discreteFourierGreenPairing d N L mass
      (periodicCosineTest d L k hL) (periodicCosineTest d L l hL) =
    if integerLatticeMode d N k = -integerLatticeMode d N k then
      (L : ℂ)^d / fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k)
    else
      ((L : ℂ)^d / fixedVolumeMassSymbol d N L mass (integerLatticeMode d N k)) / 2 := by
  classical
  have hcoef (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicCosineTest d L l hL) p =
      sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p := by
    rw [sampledFourierCoefficient_periodicCosineTest, sampledFourierCoefficient_periodicCosineTest]
    simp [hmode]
    ring
  unfold discreteFourierGreenPairing
  simp_rw [hcoef]
  exact discreteFourierGreenPairing_periodicCosineTest d N L mass hL hmass k

/-- Opposite residues negate sine coefficients and therefore the sine pairing. -/
theorem discreteFourierGreenPairing_periodicSineTest_oppositeResidue
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin d → ℤ)
    (hmode : integerLatticeMode d N k = -integerLatticeMode d N l) :
    discreteFourierGreenPairing d N L mass
      (periodicSineTest d L k hL) (periodicSineTest d L l hL) =
      - discreteFourierGreenPairing d N L mass
        (periodicSineTest d L k hL) (periodicSineTest d L k hL) := by
  classical
  have hcoef (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicSineTest d L l hL) p =
      -sampledFourierCoefficient d N L (periodicSineTest d L k hL) p := by
    rw [sampledFourierCoefficient_periodicSineTest, sampledFourierCoefficient_periodicSineTest]
    simp [hmode]
    ring
  unfold discreteFourierGreenPairing
  simp_rw [hcoef]
  simp only [mul_neg, neg_div]
  rw [Finset.sum_neg_distrib]
  simp

/-- Opposite-residue cosine/sine pairing vanishes by same-mode antisymmetry. -/
theorem discreteFourierGreenPairing_periodicCosineSineTest_oppositeResidue
    (d N : ℕ) [NeZero N] (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin d → ℤ)
    (hmode : integerLatticeMode d N k = -integerLatticeMode d N l) :
    discreteFourierGreenPairing d N L mass
      (periodicCosineTest d L k hL) (periodicSineTest d L l hL) = 0 := by
  classical
  have hcoef (p : FinLatticeSites d N) :
      sampledFourierCoefficient d N L (periodicSineTest d L l hL) p =
      -sampledFourierCoefficient d N L (periodicSineTest d L k hL) p := by
    rw [sampledFourierCoefficient_periodicSineTest, sampledFourierCoefficient_periodicSineTest]
    simp [hmode]
    ring
  have hdiag := discreteFourierGreenPairing_periodicCosineSineTest_sameMode d N L mass hL hmass k
  have hfac : (L : ℂ)⁻¹ ^ d ≠ 0 := pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr hL.ne'))
  unfold discreteFourierGreenPairing at hdiag ⊢
  simp_rw [hcoef]
  simp only [mul_neg, neg_div]
  have hsum : (∑ p : FinLatticeSites d N,
      star (sampledFourierCoefficient d N L (periodicCosineTest d L k hL) p) *
      sampledFourierCoefficient d N L (periodicSineTest d L k hL) p /
      fixedVolumeMassSymbol d N L mass p) = 0 := (mul_eq_zero.mp hdiag).resolve_left hfac
  rw [Finset.sum_neg_distrib, hsum]
  simp
end Pphi2Clean.Continuum
