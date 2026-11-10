import AImathPPhi2Clean.Periodic3DGaussianTarget

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology
open Pphi2Clean.UpstreamLattice
theorem periodic3DPeriodicResolvent_zeroCosine_pairing
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    (torusFourierGreenPairing 3 L mass
      (periodicCosineTest 3 L 0 hL) (periodicCosineTest 3 L 0 hL)).re =
        (((L : ℂ) ^ 3 / (mass : ℂ) ^ 2).re) := by
  have hper : IsFlatTorusPeriodic 3 L (periodicCosineTest 3 L 0 hL) :=
    periodicCosineTest_isFlatTorusPeriodic 3 L hL 0
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
    3 L mass hL hmass (periodicCosineTest 3 L 0 hL)
    (periodicCosineTest 3 L 0 hL) hper hper
  have hconst : ∀ n : ℕ,
      fixedVolumeCovarianceInner 3 L mass hL hmass
        (periodicCosineTest 3 L 0 hL) (periodicCosineTest 3 L 0 hL) n =
        (((L : ℂ) ^ 3 / (mass : ℂ) ^ 2).re) := by
    intro n
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    rw [discreteFourierGreenPairing_periodicCosineTest] <;> try exact hmass
    have hself : integerLatticeMode 3 (n + 1) 0 = -integerLatticeMode 3 (n + 1) 0 := by
      ext i
      simp [integerLatticeMode]
    rw [if_pos hself]
    have hs : fixedVolumeMassSymbol 3 (n + 1) L mass
        (integerLatticeMode 3 (n + 1) 0) = (mass : ℂ) ^ 2 := by
      rw [fixedVolumeMassSymbol_eq_real]
      simp [fixedVolumeMassSymbolReal, integerLatticeMode]
    rw [hs]
  have hconstlim : Filter.Tendsto
      (fun _ : ℕ => (((L : ℂ) ^ 3 / (mass : ℂ) ^ 2).re)) Filter.atTop
      (nhds (((L : ℂ) ^ 3 / (mass : ℂ) ^ 2).re)) := tendsto_const_nhds
  have heq := tendsto_nhds_unique
    (hlim.congr' (Filter.Eventually.of_forall hconst)) hconstlim
  exact heq
/-- The zero-mode sine coordinate vanishes in the continuum Green pairing. -/
theorem periodic3DPeriodicResolvent_zeroSine_pairing
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    (torusFourierGreenPairing 3 L mass
      (periodicSineTest 3 L 0 hL) (periodicSineTest 3 L 0 hL)).re = 0 := by
  have hper : IsFlatTorusPeriodic 3 L (periodicSineTest 3 L 0 hL) :=
    periodicSineTest_isFlatTorusPeriodic 3 L hL 0
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
    3 L mass hL hmass (periodicSineTest 3 L 0 hL)
    (periodicSineTest 3 L 0 hL) hper hper
  have hconst : ∀ n : ℕ,
      fixedVolumeCovarianceInner 3 L mass hL hmass
        (periodicSineTest 3 L 0 hL) (periodicSineTest 3 L 0 hL) n = 0 := by
    intro n
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    rw [discreteFourierGreenPairing_periodicSineTest] <;> try exact hmass
    have hself : integerLatticeMode 3 (n + 1) 0 = -integerLatticeMode 3 (n + 1) 0 := by
      ext i
      simp [integerLatticeMode]
    rw [if_pos hself]
    rfl
  have hconstlim : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique
    (hlim.congr' (Filter.Eventually.of_forall hconst)) hconstlim
  exact heq
theorem periodic3D_integerLatticeMode_eventually_ne_neg (k : Fin 3 → ℤ) (hk : ∃ i, k i ≠ 0) : ∀ᶠ n in Filter.atTop, integerLatticeMode 3 (n + 1) k ≠ -integerLatticeMode 3 (n + 1) k := by
  obtain ⟨i, hki⟩ := hk
  filter_upwards [eventually_gt_atTop (2 * (k i).natAbs)] with n hn
  intro hself
  have hzi : (k i : ZMod (n + 1)) = -(k i : ZMod (n + 1)) := by exact congrFun hself i
  have hzero : ((2 * k i : ℤ) : ZMod (n + 1)) = 0 := by
    push_cast
    simpa [two_mul] using (add_eq_zero_iff_eq_neg).2 hzi
  have hdiv : ((n + 1 : ℕ) : ℤ) ∣ 2 * k i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  have hdivabs : ((n + 1 : ℕ) : ℤ) ∣ |2 * k i| := (dvd_abs _ _).2 hdiv
  have habspos : 0 < |2 * k i| := by rw [abs_pos]; exact mul_ne_zero (by norm_num) hki
  have hbound := Int.le_of_dvd habspos hdivabs
  have hncast : (2 * (k i).natAbs : ℤ) < (n : ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hncast
  have habsEq : |2 * k i| = 2 * |k i| := by simp [abs_mul]
  rw [habsEq] at hbound
  omega
theorem periodic3D_nonzero_cosine_pairing_test (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (k : Fin 3 → ℤ) (hk : ∃ i, k i ≠ 0) :
    (torusFourierGreenPairing 3 L mass (periodicCosineTest 3 L k hL) (periodicCosineTest 3 L k hL)).re = ((((L : ℂ) ^ 3 / (torusMassSymbol 3 L mass k : ℂ)) / 2).re) := by
  have hper : IsFlatTorusPeriodic 3 L (periodicCosineTest 3 L k hL) := periodicCosineTest_isFlatTorusPeriodic 3 L hL k
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 3 L mass hL hmass (periodicCosineTest 3 L k hL) (periodicCosineTest 3 L k hL) hper hper
  have hnonself : ∀ᶠ n in Filter.atTop, integerLatticeMode 3 (n + 1) k ≠ -integerLatticeMode 3 (n + 1) k := periodic3D_integerLatticeMode_eventually_ne_neg k hk
  have hseq : ∀ᶠ n in Filter.atTop, fixedVolumeCovarianceInner 3 L mass hL hmass (periodicCosineTest 3 L k hL) (periodicCosineTest 3 L k hL) n = (((L : ℂ) ^ 3 / fixedVolumeMassSymbol 3 (n + 1) L mass (integerLatticeMode 3 (n + 1) k)) / 2).re := by
    filter_upwards [hnonself] with n hn
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    rw [discreteFourierGreenPairing_periodicCosineTest] <;> try exact hmass
    rw [if_neg hn]
  have hden := fixedVolumeMassSymbol_integerLatticeMode_tendsto 3 L mass k
  have hden0 : (torusMassSymbol 3 L mass k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (torusMassSymbol_pos 3 L mass hmass k).ne'
  have hnum : Filter.Tendsto (fun _ : ℕ => (L : ℂ) ^ 3) Filter.atTop (nhds ((L : ℂ) ^ 3)) := tendsto_const_nhds
  have hquot : Filter.Tendsto (fun n : ℕ => (((L : ℂ) ^ 3 / fixedVolumeMassSymbol 3 (n + 1) L mass (integerLatticeMode 3 (n + 1) k)) / 2)) Filter.atTop (nhds ((((L : ℂ) ^ 3 / (torusMassSymbol 3 L mass k : ℂ)) / 2))) := by
    simpa using (hnum.div hden hden0).div_const (2 : ℂ)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hquot
  have hlimquot : Filter.Tendsto (fun n : ℕ => (((L : ℂ) ^ 3 / fixedVolumeMassSymbol 3 (n + 1) L mass (integerLatticeMode 3 (n + 1) k)) / 2).re) Filter.atTop (nhds ((((L : ℂ) ^ 3 / (torusMassSymbol 3 L mass k : ℂ)) / 2).re)) := by
    convert hreal using 1
    · ext n
      rfl
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hlimquot
  exact heq
theorem periodic3D_nonzero_sine_pairing_test
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k : Fin 3 → ℤ) (hk : ∃ i, k i ≠ 0) :
    (torusFourierGreenPairing 3 L mass
      (periodicSineTest 3 L k hL) (periodicSineTest 3 L k hL)).re =
      ((((L : ℂ) ^ 3 / (torusMassSymbol 3 L mass k : ℂ)) / 2).re) := by
  have hper : IsFlatTorusPeriodic 3 L (periodicSineTest 3 L k hL) :=
    periodicSineTest_isFlatTorusPeriodic 3 L hL k
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
    3 L mass hL hmass (periodicSineTest 3 L k hL)
    (periodicSineTest 3 L k hL) hper hper
  have hnonself : ∀ᶠ n in Filter.atTop,
      integerLatticeMode 3 (n + 1) k ≠ -integerLatticeMode 3 (n + 1) k :=
    periodic3D_integerLatticeMode_eventually_ne_neg k hk
  have hseq : ∀ᶠ n in Filter.atTop,
      fixedVolumeCovarianceInner 3 L mass hL hmass
        (periodicSineTest 3 L k hL) (periodicSineTest 3 L k hL) n =
      (((L : ℂ) ^ 3 / fixedVolumeMassSymbol 3 (n + 1) L mass
        (integerLatticeMode 3 (n + 1) k)) / 2).re := by
    filter_upwards [hnonself] with n hn
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    rw [discreteFourierGreenPairing_periodicSineTest] <;> try exact hmass
    rw [if_neg hn]
  have hden := fixedVolumeMassSymbol_integerLatticeMode_tendsto 3 L mass k
  have hden0 : (torusMassSymbol 3 L mass k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (torusMassSymbol_pos 3 L mass hmass k).ne'
  have hnum : Filter.Tendsto (fun _ : ℕ => (L : ℂ) ^ 3)
      Filter.atTop (nhds ((L : ℂ) ^ 3)) := tendsto_const_nhds
  have hquot : Filter.Tendsto
      (fun n : ℕ => (((L : ℂ) ^ 3 /
        fixedVolumeMassSymbol 3 (n + 1) L mass (integerLatticeMode 3 (n + 1) k)) / 2))
      Filter.atTop (nhds ((((L : ℂ) ^ 3 /
        (torusMassSymbol 3 L mass k : ℂ)) / 2))) := by
    simpa using (hnum.div hden hden0).div_const (2 : ℂ)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hquot
  have hlimquot : Filter.Tendsto
      (fun n : ℕ => (((L : ℂ) ^ 3 /
        fixedVolumeMassSymbol 3 (n + 1) L mass (integerLatticeMode 3 (n + 1) k)) / 2).re)
      Filter.atTop (nhds ((((L : ℂ) ^ 3 /
        (torusMassSymbol 3 L mass k : ℂ)) / 2).re)) := by
    convert hreal using 1
    · ext n
      rfl
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hlimquot
  exact heq
theorem periodic3D_integerLatticeMode_eventually_ne_of_ne (k l : Fin 3 → ℤ) (h : k ≠ l) :
    ∀ᶠ n in Filter.atTop, integerLatticeMode 3 (n + 1) k ≠ integerLatticeMode 3 (n + 1) l := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  filter_upwards [eventually_gt_atTop ((k i - l i).natAbs)] with n hn
  intro hres
  have hzero : ((k i - l i : ℤ) : ZMod (n + 1)) = 0 := by
    have hcoord := congrFun hres i
    change (k i : ZMod (n + 1)) = (l i : ZMod (n + 1)) at hcoord
    push_cast
    exact sub_eq_zero.mpr hcoord
  have hdiv : ((n + 1 : ℕ) : ℤ) ∣ k i - l i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  have habspos : 0 < |k i - l i| := by rw [abs_pos]; exact sub_ne_zero.mpr hi
  have hbound := Int.le_of_dvd habspos ((dvd_abs _ _).2 hdiv)
  have hncast : ((k i - l i).natAbs : ℤ) < (n : ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hncast
  omega
theorem periodic3D_integerLatticeMode_eventually_ne_neg_of_ne (k l : Fin 3 → ℤ) (h : k ≠ -l) :
    ∀ᶠ n in Filter.atTop, integerLatticeMode 3 (n + 1) k ≠ -integerLatticeMode 3 (n + 1) l := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have hi' : k i + l i ≠ 0 := by
    intro hz
    exact hi ((add_eq_zero_iff_eq_neg.mp hz))
  filter_upwards [eventually_gt_atTop ((k i + l i).natAbs)] with n hn
  intro hres
  have hzero : ((k i + l i : ℤ) : ZMod (n + 1)) = 0 := by
    have hcoord := congrFun hres i
    change (k i : ZMod (n + 1)) = -(l i : ZMod (n + 1)) at hcoord
    push_cast
    exact add_eq_zero_iff_eq_neg.mpr hcoord
  have hdiv : ((n + 1 : ℕ) : ℤ) ∣ k i + l i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  have habspos : 0 < |k i + l i| := by rw [abs_pos]; exact hi'
  have hbound := Int.le_of_dvd habspos ((dvd_abs _ _).2 hdiv)
  have hncast : ((k i + l i).natAbs : ℤ) < (n : ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hncast
  omega
theorem periodic3D_cosine_cross_disjoint_test (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin 3 → ℤ) (hkl : k ≠ l) (hknl : k ≠ -l) :
    (torusFourierGreenPairing 3 L mass (periodicCosineTest 3 L k hL) (periodicCosineTest 3 L l hL)).re = 0 := by
  have hperK := periodicCosineTest_isFlatTorusPeriodic 3 L hL k
  have hperL := periodicCosineTest_isFlatTorusPeriodic 3 L hL l
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 3 L mass hL hmass
    (periodicCosineTest 3 L k hL) (periodicCosineTest 3 L l hL) hperK hperL
  have hevents := (periodic3D_integerLatticeMode_eventually_ne_of_ne k l hkl).and
    (periodic3D_integerLatticeMode_eventually_ne_neg_of_ne k l hknl)
  have hseq : ∀ᶠ n in Filter.atTop, fixedVolumeCovarianceInner 3 L mass hL hmass
      (periodicCosineTest 3 L k hL) (periodicCosineTest 3 L l hL) n = 0 := by
    filter_upwards [hevents] with n hn
    rcases hn with ⟨h1, h2⟩
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    have h3 : -integerLatticeMode 3 (n + 1) k ≠ integerLatticeMode 3 (n + 1) l := by
      intro h
      apply h2
      simpa using congrArg Neg.neg h
    have h4 : -integerLatticeMode 3 (n + 1) k ≠ -integerLatticeMode 3 (n + 1) l := by
      intro h
      apply h1
      exact neg_injective h
    rw [discreteFourierGreenPairing_periodicCosineTest_disjoint]
    · rfl
    · exact hmass
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hzero
  exact heq

theorem periodic3D_sine_cross_disjoint_test (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (k l : Fin 3 → ℤ) (hkl : k ≠ l) (hknl : k ≠ -l) :
    (torusFourierGreenPairing 3 L mass (periodicSineTest 3 L k hL) (periodicSineTest 3 L l hL)).re = 0 := by
  have hperK := periodicSineTest_isFlatTorusPeriodic 3 L hL k
  have hperL := periodicSineTest_isFlatTorusPeriodic 3 L hL l
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 3 L mass hL hmass
    (periodicSineTest 3 L k hL) (periodicSineTest 3 L l hL) hperK hperL
  have hevents := (periodic3D_integerLatticeMode_eventually_ne_of_ne k l hkl).and
    (periodic3D_integerLatticeMode_eventually_ne_neg_of_ne k l hknl)
  have hseq : ∀ᶠ n in Filter.atTop, fixedVolumeCovarianceInner 3 L mass hL hmass
      (periodicSineTest 3 L k hL) (periodicSineTest 3 L l hL) n = 0 := by
    filter_upwards [hevents] with n hn
    rcases hn with ⟨h1, h2⟩
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    have h3 : -integerLatticeMode 3 (n + 1) k ≠ integerLatticeMode 3 (n + 1) l := by
      intro h; apply h2; simpa using congrArg Neg.neg h
    have h4 : -integerLatticeMode 3 (n + 1) k ≠ -integerLatticeMode 3 (n + 1) l := by
      intro h; apply h1; exact neg_injective h
    rw [discreteFourierGreenPairing_periodicSineTest_disjoint]
    · rfl
    · exact hmass
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hzero
  exact heq
theorem periodic3D_cosine_sine_cross_test (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (k l : Fin 3 → ℤ) :
    (torusFourierGreenPairing 3 L mass (periodicCosineTest 3 L k hL) (periodicSineTest 3 L l hL)).re = 0 := by
  have hperK := periodicCosineTest_isFlatTorusPeriodic 3 L hL k
  have hperL := periodicSineTest_isFlatTorusPeriodic 3 L hL l
  have hlim := fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing 3 L mass hL hmass (periodicCosineTest 3 L k hL) (periodicSineTest 3 L l hL) hperK hperL
  have hfinite (n : ℕ) : fixedVolumeCovarianceInner 3 L mass hL hmass (periodicCosineTest 3 L k hL) (periodicSineTest 3 L l hL) n = 0 := by
    letI : NeZero (n + 1) := ⟨(Nat.succ_pos n).ne'⟩
    rw [fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing]
    let q := integerLatticeMode 3 (n + 1) k
    let r := integerLatticeMode 3 (n + 1) l
    by_cases hqr : q = r
    · have hcoef (p : FinLatticeSites 3 (n + 1)) : sampledFourierCoefficient 3 (n + 1) L (periodicSineTest 3 L l hL) p = sampledFourierCoefficient 3 (n + 1) L (periodicSineTest 3 L k hL) p := by
        rw [sampledFourierCoefficient_periodicSineTest, sampledFourierCoefficient_periodicSineTest]
        simp [q, r, hqr] <;> ring
      have hdiag := discreteFourierGreenPairing_periodicCosineSineTest_sameMode 3 (n + 1) L mass hL hmass k
      unfold discreteFourierGreenPairing at hdiag ⊢
      simp_rw [hcoef]
      exact congrArg Complex.re hdiag
    · by_cases hqnr : q = -r
      · have hcoef (p : FinLatticeSites 3 (n + 1)) : sampledFourierCoefficient 3 (n + 1) L (periodicSineTest 3 L l hL) p = -sampledFourierCoefficient 3 (n + 1) L (periodicSineTest 3 L k hL) p := by
          rw [sampledFourierCoefficient_periodicSineTest, sampledFourierCoefficient_periodicSineTest]
          simp [q, r, hqnr] <;> ring
        have hdiag := discreteFourierGreenPairing_periodicCosineSineTest_sameMode 3 (n + 1) L mass hL hmass k
        unfold discreteFourierGreenPairing at hdiag ⊢
        simp_rw [hcoef]
        simp only [mul_neg, neg_div]
        have hsum := neg_eq_zero.mpr hdiag
        simpa only [Finset.sum_neg_distrib, mul_neg, Complex.neg_re, Complex.zero_re] using congrArg Complex.re hsum
      · have hnr : -q ≠ r := by intro hz; apply hqnr; simpa using congrArg Neg.neg hz
        have hnn : -q ≠ -r := by intro hz; apply hqr; exact neg_injective hz
        have hdis := discreteFourierGreenPairing_periodicCosineSineTest_disjoint 3 (n + 1) L mass hL hmass k l
          (by simpa [q, r] using hqr) (by simpa [q, r] using hqnr)
          (by simpa [q, r] using hnr) (by simpa [q, r] using hnn)
        exact congrArg Complex.re hdis
  have hseq : ∀ᶠ n in Filter.atTop, fixedVolumeCovarianceInner 3 L mass hL hmass (periodicCosineTest 3 L k hL) (periodicSineTest 3 L l hL) n = 0 := Filter.Eventually.of_forall hfinite
  have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique (hlim.congr' hseq) hzero
  exact heq
end Pphi2Clean.Continuum

namespace Pphi2Clean.Continuum

end Pphi2Clean.Continuum
