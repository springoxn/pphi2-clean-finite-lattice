import AImathPPhi2Clean.TightnessChebyshev

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory

/-- The coordinate box for a countable family of real observables. -/
def observableBox {X : Type*} (f : ℕ → X → ℝ) (R : ℕ → ℝ) : Set X :=
  {x | ∀ n, |f n x| ≤ R n}

/-- Countable subadditivity and uniform second moments control the mass
outside a coordinate box. No topological assumption is used here. -/
theorem observableBox_compl_le
    {ι X : Type*} [MeasurableSpace X]
    (μ : ι → Measure X) (f : ℕ → X → ℝ) (R C : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (h_int : ∀ n i, Integrable (fun x => f n x ^ 2) (μ i))
    (h_moment : ∀ n i, ∫ x, f n x ^ 2 ∂(μ i) ≤ C n) :
    ∀ i, μ i (observableBox f R)ᶜ ≤
      ∑' n, ENNReal.ofReal (C n / R n ^ 2) := by
  intro i
  have hsub : (observableBox f R)ᶜ ⊆ ⋃ n, {x | R n ≤ |f n x|} := by
    intro x hx
    have hx' : ¬ ∀ n, |f n x| ≤ R n := hx
    push Not at hx'
    obtain ⟨n, hn⟩ := hx'
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  calc
    μ i (observableBox f R)ᶜ ≤ μ i (⋃ n, {x | R n ≤ |f n x|}) := measure_mono hsub
    _ ≤ ∑' n, μ i {x | R n ≤ |f n x|} := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (C n / R n ^ 2) := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact uniform_second_moment_tail_bound μ (f n) (R n) (C n)
        (hR n) (h_int n) (h_moment n) i

/-- Coordinate boxes are compact in the product topology on real sequences.
This does not assert compactness of their preimages in a different topology. -/
theorem sequence_observableBox_isCompact (R : ℕ → ℝ) :
    IsCompact (observableBox (fun n (x : ℕ → ℝ) => x n) R) := by
  have hset : observableBox (fun n (x : ℕ → ℝ) => x n) R =
      Set.pi Set.univ (fun n => Set.Icc (-(R n)) (R n)) := by
    ext x
    constructor
    · intro hx n hn
      exact abs_le.mp (hx n)
    · intro hx n
      exact abs_le.mpr (hx n (Set.mem_univ n))
  rw [hset]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- A summable coordinate tail budget produces a common compact box for
measures on real sequences, with the product topology. -/
theorem sequence_compact_containment_of_tail_budget
    {ι : Type*} (μ : ι → Measure (ℕ → ℝ)) (R C : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (h_int : ∀ n i, Integrable (fun x => x n ^ 2) (μ i))
    (h_moment : ∀ n i, ∫ x, x n ^ 2 ∂(μ i) ≤ C n)
    (ε : ENNReal) (h_budget : (∑' n, ENNReal.ofReal (C n / R n ^ 2)) ≤ ε) :
    ∃ K : Set (ℕ → ℝ), IsCompact K ∧ ∀ i, μ i Kᶜ ≤ ε := by
  refine ⟨observableBox (fun n x => x n) R, sequence_observableBox_isCompact R, ?_⟩
  intro i
  exact (observableBox_compl_le μ (fun n x => x n) R C hR h_int h_moment i).trans h_budget

end Pphi2Clean.Continuum
