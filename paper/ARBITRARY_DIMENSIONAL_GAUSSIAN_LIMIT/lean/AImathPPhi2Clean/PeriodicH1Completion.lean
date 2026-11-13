import AImathPPhi2Clean.PeriodicMassiveWeakSolver
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section
open scoped Topology BigOperators lp
namespace Pphi2Clean.Continuum

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The physical value and all first gradients, with the usual product norm. -/
def h1Graph (d : ℕ) (j : H →L[ℂ] E) (D : Fin d → H →L[ℂ] E) :
    H →L[ℂ] E × (Fin d → E) :=
  j.prod (ContinuousLinearMap.pi D)

@[simp] theorem h1Graph_apply (d : ℕ) (j : H →L[ℂ] E)
    (D : Fin d → H →L[ℂ] E) (h : H) :
    h1Graph d j D h = (j h, fun i => D i h) := rfl

/-- An energy splitting gives a lower bound on the full value-gradient graph.
The deliberately nonsharp constant works also for zero coordinates. -/
theorem h1Graph_lower_bound (d : ℕ) (mass : ℝ)
    (j : H →L[ℂ] E) (D : Fin d → H →L[ℂ] E)
    (hsplit : ∀ h : H, ‖h‖ ^ 2 = mass ^ 2 * ‖j h‖ ^ 2 + ∑ i, ‖D i h‖ ^ 2)
    (h : H) : ‖h‖ ≤ (mass ^ 2 + (d : ℝ) + 1) * ‖h1Graph d j D h‖ := by
  let b := ‖h1Graph d j D h‖
  have hb : 0 ≤ b := norm_nonneg _
  have hj : ‖j h‖ ≤ b := norm_fst_le (h1Graph d j D h)
  have hD (i : Fin d) : ‖D i h‖ ≤ b :=
    (norm_le_pi_norm (fun i => D i h) i).trans (norm_snd_le (h1Graph d j D h))
  have hsum : (∑ i : Fin d, ‖D i h‖ ^ 2) ≤ (d : ℝ) * b ^ 2 := by
    calc
      _ ≤ ∑ i : Fin d, b ^ 2 := Finset.sum_le_sum (fun i _ => by
        nlinarith [norm_nonneg (D i h), hD i])
      _ = _ := by simp
  have hmass : mass ^ 2 * ‖j h‖ ^ 2 ≤ mass ^ 2 * b ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (j h)]) (sq_nonneg mass)
  have hsq : ‖h‖ ^ 2 ≤ (mass ^ 2 + (d : ℝ)) * b ^ 2 := by
    rw [hsplit]
    nlinarith only [hsum, hmass]
  have hc : 0 ≤ mass ^ 2 + (d : ℝ) := by positivity
  have hC : 0 ≤ (mass ^ 2 + (d : ℝ) + 1) * b := by positivity
  have hfactor : 0 ≤ ((mass ^ 2 + (d : ℝ) + 1) ^ 2 - (mass ^ 2 + (d : ℝ))) * b ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    nlinarith [sq_nonneg (mass ^ 2 + (d : ℝ))]
  nlinarith [norm_nonneg h]

/-- Completeness plus the energy identity makes the gradient graph closed. -/
theorem h1Graph_isClosed_range [CompleteSpace H]
    (d : ℕ) (mass : ℝ) (j : H →L[ℂ] E) (D : Fin d → H →L[ℂ] E)
    (hsplit : ∀ h : H, ‖h‖ ^ 2 = mass ^ 2 * ‖j h‖ ^ 2 + ∑ i, ‖D i h‖ ^ 2) :
    IsClosed (Set.range (h1Graph d j D)) := by
  let C : NNReal := ⟨mass ^ 2 + (d : ℝ) + 1, by positivity⟩
  have ha : AntilipschitzWith C (h1Graph d j D) :=
    (h1Graph d j D).antilipschitz_of_bound (fun h => h1Graph_lower_bound d mass j D hsplit h)
  exact ha.isClosed_range (h1Graph d j D).uniformContinuous

/-- A dense core determines exactly the complete closed value-gradient graph. -/
theorem h1Graph_range_eq_closure_image [CompleteSpace H]
    (d : ℕ) (mass : ℝ) (j : H →L[ℂ] E) (D : Fin d → H →L[ℂ] E)
    (hsplit : ∀ h : H, ‖h‖ ^ 2 = mass ^ 2 * ‖j h‖ ^ 2 + ∑ i, ‖D i h‖ ^ 2)
    (s : Set H) (hs : Dense s) :
    Set.range (h1Graph d j D) = closure ((h1Graph d j D) '' s) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨h, rfl⟩
    exact image_closure_subset_closure_image (h1Graph d j D).continuous
      ⟨h, hs h, rfl⟩
  · exact closure_minimal (Set.image_subset_range _ _)
      (h1Graph_isClosed_range d mass j D hsplit)

/-- Energy vectors supported on a finite frequency set. -/
def finiteSupportEnergy (ι : Type*) : Set (MassiveEnergy ι) :=
  {h | ∃ s : Finset ι, ∀ k, k ∉ s → h k = 0}

theorem finiteSupportEnergy_dense (ι : Type*) : Dense (finiteSupportEnergy ι) := by
  classical
  intro h
  apply isClosed_closure.mem_of_tendsto (finiteSupport_tendsto h)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨s, ?_⟩
  intro k hk
  simp only [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  simp [lp.single_apply, ne_of_mem_of_not_mem hi hk]

/-- The full graph is exactly the closure of finite-frequency graphs. Parent
modules identify these finite graphs with classical trigonometric derivatives. -/
theorem massiveEnergy_graph_completion {ι : Type*}
    (d : ℕ) (mass : ℝ) (j : MassiveEnergy ι →L[ℂ] E)
    (D : Fin d → MassiveEnergy ι →L[ℂ] E)
    (hsplit : ∀ h : MassiveEnergy ι,
      ‖h‖ ^ 2 = mass ^ 2 * ‖j h‖ ^ 2 + ∑ i, ‖D i h‖ ^ 2) :
    Set.range (h1Graph d j D) =
      closure ((h1Graph d j D) '' finiteSupportEnergy ι) :=
  h1Graph_range_eq_closure_image d mass j D hsplit _ (finiteSupportEnergy_dense ι)

end Pphi2Clean.Continuum
