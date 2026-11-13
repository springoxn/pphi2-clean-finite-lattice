import AImathPPhi2Clean.Periodic3DTargetMarginalBridge
import AImathPPhi2Clean.Periodic3DModePairing

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory Filter Topology Pphi2Clean.UpstreamLattice

def periodic3DPhysicalCoordinateTest (L : ℝ) (hL : 0 < L)
    (j : FS4GaussianRealCoordinateIndex) : BoundedContinuousFunction (Fin 3 → ℝ) ℝ :=
  j.elim (fun _ => periodicCosineTest 3 L 0 hL) (fun q =>
    if q.2 then periodicSineTest 3 L (periodic3DRestrictIndex q.1.1) hL
    else periodicCosineTest 3 L (periodic3DRestrictIndex q.1.1) hL)

theorem periodic3DPhysicalCoordinateTest_periodic (L : ℝ) (hL : 0 < L)
    (j : FS4GaussianRealCoordinateIndex) :
    IsFlatTorusPeriodic 3 L (periodic3DPhysicalCoordinateTest L hL j) := by
  rcases j with u | ⟨k,b⟩
  · exact periodicCosineTest_isFlatTorusPeriodic 3 L hL 0
  · cases b
    · exact periodicCosineTest_isFlatTorusPeriodic 3 L hL _
    · exact periodicSineTest_isFlatTorusPeriodic 3 L hL _

theorem periodic3DRestrictIndex_eq_iff (k l : FS4Index)
    (hk : k 3 = 0) (hl : l 3 = 0) :
    periodic3DRestrictIndex k = periodic3DRestrictIndex l ↔ k = l := by
  constructor
  · intro h
    have he := congrArg periodic3DExtend h
    simpa only [periodic3DExtend_restrictIndex_of_fourth_zero k hk,
      periodic3DExtend_restrictIndex_of_fourth_zero l hl] using he
  · rintro rfl
    rfl

theorem periodic3DRestrictIndex_canonical_ne_zero (k : FS4CanonicalPairIndex)
    (hk : k.1 3 = 0) : periodic3DRestrictIndex k.1 ≠ 0 := by
  intro h
  apply k.2.1
  apply (periodic3DRestrictIndex_eq_iff k.1 0 hk (by simp)).mp
  exact h

theorem periodic3DRestrictIndex_canonical_ne_neg (k l : FS4CanonicalPairIndex)
    (hk : k.1 3 = 0) (hl : l.1 3 = 0) :
    periodic3DRestrictIndex k.1 ≠ -periodic3DRestrictIndex l.1 := by
  intro h
  apply fs4CanonicalPair_not_neg_of_canonical k.1 l.1 k.2 l.2
  apply (periodic3DRestrictIndex_eq_iff k.1 (-l.1) hk (by simp [hl])).mp
  exact h

theorem periodic3DPhysicalCoordinateTest_diagonal (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (j : FS4GaussianRealCoordinateIndex)
    (hsupport : j.elim (fun _ => True) (fun q => q.1.1 3 = 0)) :
    (torusFourierGreenPairing 3 L mass (periodic3DPhysicalCoordinateTest L hL j)
      (periodic3DPhysicalCoordinateTest L hL j)).re =
        (fs4PhysicalRealCoordinateScale L mass j)^2 / L := by
  rcases j with u | ⟨k,b⟩
  · change (torusFourierGreenPairing 3 L mass (periodicCosineTest 3 L 0 hL)
      (periodicCosineTest 3 L 0 hL)).re = (L^2 / mass)^2 / L
    rw [periodic3DPeriodicResolvent_zeroCosine_pairing L mass hL hmass]
    have hc : (((L : ℂ)^3 / (mass : ℂ)^2).re) = L^3 / mass^2 := by norm_cast
    rw [hc]
    field_simp
  · have hk0 : k.1 3 = 0 := hsupport
    have hk : ∃ i, periodic3DRestrictIndex k.1 i ≠ 0 := by
      simpa only [Pi.zero_apply] using
        Function.ne_iff.mp (periodic3DRestrictIndex_canonical_ne_zero k hk0)
    rw [periodic3D_fourthZeroCanonicalScale_variance L mass hL hmass k hk0 b]
    have hc : ((((L : ℂ)^3 /
        (torusMassSymbol 3 L mass (periodic3DRestrictIndex k.1) : ℂ))/2).re) =
        (L^3 / torusMassSymbol 3 L mass (periodic3DRestrictIndex k.1))/2 := by norm_cast
    cases b
    · change (torusFourierGreenPairing 3 L mass
        (periodicCosineTest 3 L (periodic3DRestrictIndex k.1) hL)
        (periodicCosineTest 3 L (periodic3DRestrictIndex k.1) hL)).re = _
      rw [periodic3D_nonzero_cosine_pairing_test L mass hL hmass _ hk, hc]
      unfold periodic3DCanonicalPairVariance
      ring
    · change (torusFourierGreenPairing 3 L mass
        (periodicSineTest 3 L (periodic3DRestrictIndex k.1) hL)
        (periodicSineTest 3 L (periodic3DRestrictIndex k.1) hL)).re = _
      rw [periodic3D_nonzero_sine_pairing_test L mass hL hmass _ hk, hc]
      unfold periodic3DCanonicalPairVariance
      ring

theorem periodic3DPhysicalCoordinateTest_zero_cross (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : FS4CanonicalPairIndex)
    (hk0 : k.1 3 = 0) (b : Bool) :
    (torusFourierGreenPairing 3 L mass
      (periodic3DPhysicalCoordinateTest L hL (Sum.inl ()))
      (periodic3DPhysicalCoordinateTest L hL (Sum.inr (k,b)))).re = 0 := by
  have hk := periodic3DRestrictIndex_canonical_ne_zero k hk0
  have hn : (0 : Periodic3DIndex) ≠ -periodic3DRestrictIndex k.1 := by
    simpa only [ne_eq, zero_eq_neg] using hk
  cases b
  · exact periodic3D_cosine_cross_disjoint_test L mass hL hmass 0 _ (Ne.symm hk) hn
  · exact periodic3D_cosine_sine_cross_test L mass hL hmass 0 _

theorem periodic3DPhysicalCoordinateTest_cross (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (j q : FS4GaussianRealCoordinateIndex)
    (hj : j.elim (fun _ => True) (fun p => p.1.1 3 = 0))
    (hq : q.elim (fun _ => True) (fun p => p.1.1 3 = 0)) (hjq : j ≠ q) :
    (torusFourierGreenPairing 3 L mass (periodic3DPhysicalCoordinateTest L hL j)
      (periodic3DPhysicalCoordinateTest L hL q)).re = 0 := by
  rcases j with u | ⟨k,b⟩ <;> rcases q with v | ⟨l,c⟩
  · cases u; cases v; exact (hjq rfl).elim
  · cases u
    exact periodic3DPhysicalCoordinateTest_zero_cross L mass hL hmass l hq c
  · cases v
    rw [torusFourierGreenPairing_symm]
    exact periodic3DPhysicalCoordinateTest_zero_cross L mass hL hmass k hj b
  · have hn := periodic3DRestrictIndex_canonical_ne_neg k l hj hq
    cases b <;> cases c
    · have hkl : periodic3DRestrictIndex k.1 ≠ periodic3DRestrictIndex l.1 := by
        intro h
        apply hjq
        congr 2
        exact Subtype.ext ((periodic3DRestrictIndex_eq_iff k.1 l.1 hj hq).mp h)
      exact periodic3D_cosine_cross_disjoint_test L mass hL hmass _ _ hkl hn
    · exact periodic3D_cosine_sine_cross_test L mass hL hmass _ _
    · rw [torusFourierGreenPairing_symm]
      exact periodic3D_cosine_sine_cross_test L mass hL hmass _ _
    · have hkl : periodic3DRestrictIndex k.1 ≠ periodic3DRestrictIndex l.1 := by
        intro h
        apply hjq
        congr 2
        exact Subtype.ext ((periodic3DRestrictIndex_eq_iff k.1 l.1 hj hq).mp h)
      exact periodic3D_sine_cross_disjoint_test L mass hL hmass _ _ hkl hn

theorem periodic3DPhysicalCoordinateTest_covariance (L mass : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (j q : FS4GaussianRealCoordinateIndex)
    (hj : j.elim (fun _ => True) (fun p => p.1.1 3 = 0))
    (hq : q.elim (fun _ => True) (fun p => p.1.1 3 = 0)) :
    (torusFourierGreenPairing 3 L mass (periodic3DPhysicalCoordinateTest L hL j)
      (periodic3DPhysicalCoordinateTest L hL q)).re =
      if j = q then (fs4PhysicalRealCoordinateScale L mass j)^2 / L else 0 := by
  classical
  by_cases h : j = q
  · subst q
    rw [if_pos rfl]
    exact periodic3DPhysicalCoordinateTest_diagonal L mass hL hmass j hj
  · rw [if_neg h]
    exact periodic3DPhysicalCoordinateTest_cross L mass hL hmass j q hj hq h

theorem periodic3DPhysicalCoordinateTest_resolventCovarianceMatrix
    (m : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (js : Fin m → FS4GaussianRealCoordinateIndex) (hjs : Function.Injective js)
    (hsupport : ∀ i, (js i).elim (fun _ => True) (fun p => p.1.1 3 = 0))
    (i j : Fin m) :
    periodicResolventCovarianceMatrix 3 m L mass hmass
      (fun i => periodic3DPhysicalCoordinateTest L hL (js i)) i j =
      if i = j then (fs4PhysicalRealCoordinateScale L mass (js i))^2 / L else 0 := by
  classical
  unfold periodicResolventCovarianceMatrix
  rw [← torusFourierGreenPairing_eq_physicalTorusResolventPairing 3 L mass hL hmass]
  rw [periodic3DPhysicalCoordinateTest_covariance L mass hL hmass _ _
    (hsupport i) (hsupport j)]
  simp only [hjs.eq_iff]

end Pphi2Clean.Continuum
