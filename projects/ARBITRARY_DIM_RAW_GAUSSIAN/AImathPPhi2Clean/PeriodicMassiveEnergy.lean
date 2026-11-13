import AImathPPhi2Clean.PeriodicMassiveWeakSolver
import AImathPPhi2Clean.PeriodicFourierCovarianceLimit

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace lp
namespace Pphi2Clean.Continuum

def periodicCoordinateFrequency (d : ℕ) (L : ℝ) (i : Fin d) (k : Fin d → ℤ) : ℝ :=
  (2 * Real.pi / L) * (k i : ℝ)

theorem torusMassSymbol_eq_mass_add_frequencies (d : ℕ) (L mass : ℝ) (k : Fin d → ℤ) :
    torusMassSymbol d L mass k = mass ^ 2 + ∑ i, periodicCoordinateFrequency d L i k ^ 2 := by
  simp only [periodicCoordinateFrequency, mul_pow, ← Finset.mul_sum, torusMassSymbol]

theorem mass_sq_le_torusMassSymbol (d : ℕ) (L mass : ℝ) (k : Fin d → ℤ) :
    mass ^ 2 ≤ torusMassSymbol d L mass k := by
  rw [torusMassSymbol_eq_mass_add_frequencies]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

def periodicMassiveEmbedding (d : ℕ) (L mass : ℝ) (hmass : 0 < mass) :
    MassiveEnergyEmbedding (Fin d → ℤ) :=
  massiveEmbedding mass hmass (torusMassSymbol d L mass)
    (mass_sq_le_torusMassSymbol d L mass)

theorem periodicMassiveEmbedding_weight_sq (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (k : Fin d → ℤ) :
    (periodicMassiveEmbedding d L mass hmass).weight k ^ 2 =
      (torusMassSymbol d L mass k)⁻¹ := by
  change (Real.sqrt (torusMassSymbol d L mass k))⁻¹ ^ 2 = _
  rw [inv_pow, Real.sq_sqrt (torusMassSymbol_pos d L mass hmass k).le]

theorem periodicCoordinateFrequency_sq_le (d : ℕ) (L mass : ℝ)
    (i : Fin d) (k : Fin d → ℤ) :
    periodicCoordinateFrequency d L i k ^ 2 ≤ torusMassSymbol d L mass k := by
  rw [torusMassSymbol_eq_mass_add_frequencies]
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
    sq_nonneg (periodicCoordinateFrequency d L j k)) (Finset.mem_univ i)
  linarith [sq_nonneg mass]

theorem periodicGradient_multiplier_bound (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (i : Fin d) (k : Fin d → ℤ) :
    ‖Complex.I * (periodicCoordinateFrequency d L i k : ℂ) *
      ((periodicMassiveEmbedding d L mass hmass).weight k : ℂ)‖ ≤ 1 := by
  have hq := periodicCoordinateFrequency_sq_le d L mass i k
  have hpos := torusMassSymbol_pos d L mass hmass k
  have habs : |periodicCoordinateFrequency d L i k| ≤ Real.sqrt (torusMassSymbol d L mass k) :=
    Real.abs_le_sqrt hq
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ((periodicMassiveEmbedding d L mass hmass).weight_pos k)]
  change |periodicCoordinateFrequency d L i k| * (Real.sqrt (torusMassSymbol d L mass k))⁻¹ ≤ 1
  exact (mul_inv_le_iff₀ (Real.sqrt_pos.mpr hpos)).mpr (by simpa using habs)

def periodicEnergyGradient (d : ℕ) (L mass : ℝ) (hmass : 0 < mass) (i : Fin d) :
    MassiveEnergy (Fin d → ℤ) →L[ℂ] MassiveEnergy (Fin d → ℤ) :=
  energyMultiplier (fun k => Complex.I * (periodicCoordinateFrequency d L i k : ℂ) *
    ((periodicMassiveEmbedding d L mass hmass).weight k : ℂ)) 1 zero_le_one
    (periodicGradient_multiplier_bound d L mass hmass i)

@[simp] theorem periodicEnergyGradient_apply (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (i : Fin d) (h : MassiveEnergy (Fin d → ℤ)) (k : Fin d → ℤ) :
    periodicEnergyGradient d L mass hmass i h k =
      Complex.I * (periodicCoordinateFrequency d L i k : ℂ) *
      ((periodicMassiveEmbedding d L mass hmass).weight k : ℂ) * h k := rfl

/-- The abstract Hilbert inner product is exactly the physical massive
Dirichlet form: mass squared L2 plus all coordinate gradient pairings. -/
theorem periodicMassiveEnergy_inner_split (d : ℕ) (L mass : ℝ) (hmass : 0 < mass)
    (h v : MassiveEnergy (Fin d → ℤ)) :
    ⟪h, v⟫_ℂ = (mass ^ 2 : ℝ) •
      ⟪(periodicMassiveEmbedding d L mass hmass).inclusion h,
        (periodicMassiveEmbedding d L mass hmass).inclusion v⟫_ℂ +
      ∑ i, ⟪periodicEnergyGradient d L mass hmass i h,
        periodicEnergyGradient d L mass hmass i v⟫_ℂ := by
  classical
  let A := periodicMassiveEmbedding d L mass hmass
  have hpoint (k : Fin d → ℤ) :
      ⟪h k, v k⟫_ℂ = (mass ^ 2 : ℝ) • ⟪A.inclusion h k, A.inclusion v k⟫_ℂ +
        ∑ i, ⟪periodicEnergyGradient d L mass hmass i h k,
          periodicEnergyGradient d L mass hmass i v k⟫_ℂ := by
    have hw : (mass ^ 2 + ∑ i, periodicCoordinateFrequency d L i k ^ 2) * A.weight k ^ 2 = 1 := by
      rw [← torusMassSymbol_eq_mass_add_frequencies, periodicMassiveEmbedding_weight_sq]
      exact mul_inv_cancel₀ (torusMassSymbol_pos d L mass hmass k).ne'
    have hwc := congrArg (fun x : ℝ => (x : ℂ)) hw
    push_cast at hwc
    simp only [RCLike.inner_apply, Complex.real_smul]
    change v k * conj (h k) = ((mass ^ 2 : ℝ) : ℂ) *
      (((A.weight k : ℂ) * v k) * conj ((A.weight k : ℂ) * h k)) +
      ∑ i, (Complex.I * (periodicCoordinateFrequency d L i k : ℂ) *
        (A.weight k : ℂ) * v k) * conj (Complex.I *
        (periodicCoordinateFrequency d L i k : ℂ) * (A.weight k : ℂ) * h k)
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_pow]
    have hterm (i : Fin d) :
        (Complex.I * (periodicCoordinateFrequency d L i k : ℂ) * (A.weight k : ℂ) * v k) *
          (-(Complex.I) * (periodicCoordinateFrequency d L i k : ℂ) * (A.weight k : ℂ) * conj (h k)) =
        (periodicCoordinateFrequency d L i k : ℂ) ^ 2 * (A.weight k : ℂ) ^ 2 *
          (v k * conj (h k)) := by
      ring_nf
      simp [Complex.I_sq]
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    calc
      v k * conj (h k) = 1 * (v k * conj (h k)) := (one_mul _).symm
      _ = _ := by rw [← hwc]; ring
  have hs := ((lp.hasSum_inner (𝕜 := ℂ) (A.inclusion h) (A.inclusion v)).const_smul (mass ^ 2 : ℝ)).add
    (hasSum_sum (s := Finset.univ) (fun i _ => lp.hasSum_inner (𝕜 := ℂ)
      (periodicEnergyGradient d L mass hmass i h) (periodicEnergyGradient d L mass hmass i v)))
  exact (lp.hasSum_inner (𝕜 := ℂ) h v).unique (hs.congr_fun hpoint)

alias periodicEnergy_inner_split := periodicMassiveEnergy_inner_split

end Pphi2Clean.Continuum
