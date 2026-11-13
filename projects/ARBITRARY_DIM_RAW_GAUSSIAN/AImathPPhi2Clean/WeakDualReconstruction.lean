/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Reconstruction core adapted from GaussianField/Tightness.lean:
Mathlib-only proof with explicit summability, seminorm domination, and
basis-expansion hypotheses replacing the Dynin-Mityagin dependency.
-/
import AImathPPhi2Clean.CoordinateTightness

noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- Reconstruct a continuous linear functional from bounded coordinates.
The continuous seminorm domination is an explicit analytic input. -/
def reconstructWeakDual
    (coeff : ℕ → E →ₗ[ℝ] ℝ) (R : ℕ → ℝ)
    (hsum : ∀ f, Summable (fun n => |coeff n f| * R n))
    (q : Seminorm ℝ E) (hq : Continuous q)
    (hdom : ∀ f, (∑' n, |coeff n f| * R n) ≤ q f)
    (x : ↥(observableBox (fun n (x : ℕ → ℝ) => x n) R)) : WeakDual ℝ E := by
  have habs : ∀ n, |x.val n| ≤ R n := x.property
  have hseries : ∀ f, Summable (fun n => coeff n f * x.val n) := by
    intro f
    apply (hsum f).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (habs n) (abs_nonneg _)
  let L : E →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑' n, coeff n f * x.val n
      map_add' := fun f g => by
        simp only [map_add, add_mul]
        exact (hseries f).tsum_add (hseries g)
      map_smul' := fun c f => by
        simp only [map_smul, smul_eq_mul, mul_assoc]
        exact tsum_mul_left }
  have hbound : ∀ f, |L f| ≤ q f := by
    intro f
    calc
      |L f| ≤ ∑' n, ‖coeff n f * x.val n‖ := by
        change |∑' n, coeff n f * x.val n| ≤ _
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hseries f).norm
      _ ≤ ∑' n, |coeff n f| * R n := by
        apply (hseries f).norm.tsum_le_tsum _ (hsum f)
        intro n
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (habs n) (abs_nonneg _)
      _ ≤ q f := hdom f
  have hcont : Continuous L := by
    apply continuous_of_continuousAt_zero L.toAddMonoidHom
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    have hneigh : {f : E | q f < ε} ∈ nhds (0 : E) :=
      (hq.isOpen_preimage _ isOpen_Iio).mem_nhds (by simpa using hε)
    apply Filter.mem_of_superset hneigh
    intro f hf
    simp only [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt (hbound f) hf
  exact ⟨L, hcont⟩

/-- Reconstruction depends continuously on bounded coordinates for the weak
(topology of evaluation) dual. -/
theorem reconstructWeakDual_continuous
    (coeff : ℕ → E →ₗ[ℝ] ℝ) (R : ℕ → ℝ)
    (hsum : ∀ f, Summable (fun n => |coeff n f| * R n))
    (q : Seminorm ℝ E) (hq : Continuous q)
    (hdom : ∀ f, (∑' n, |coeff n f| * R n) ≤ q f) :
    Continuous (reconstructWeakDual coeff R hsum q hq hdom) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact continuous_tsum
    (f := fun n (x : ↥(observableBox (fun n (x : ℕ → ℝ) => x n) R)) => coeff n f * x.val n)
    (u := fun n => |coeff n f| * R n)
    (fun n => continuous_const.mul ((continuous_apply n).comp continuous_subtype_val))
    (hsum f)
    (fun n x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (x.property n) (abs_nonneg _))

/-- A weak-dual coordinate box is compact when coefficient reconstruction is
summable, dominated by a continuous seminorm, and expands every dual element.
These hypotheses still need a concrete Dynin-Mityagin instantiation for PPH2. -/
theorem weakDual_coordinateBox_isCompact
    (basis : ℕ → E) (coeff : ℕ → E →ₗ[ℝ] ℝ) (R : ℕ → ℝ)
    (hsum : ∀ f, Summable (fun n => |coeff n f| * R n))
    (q : Seminorm ℝ E) (hq : Continuous q)
    (hdom : ∀ f, (∑' n, |coeff n f| * R n) ≤ q f)
    (hexpand : ∀ (ω : WeakDual ℝ E) f,
      ω f = ∑' n, coeff n f * ω (basis n)) :
    IsCompact (observableBox (fun n (ω : WeakDual ℝ E) => ω (basis n)) R) := by
  let box := observableBox (fun n (x : ℕ → ℝ) => x n) R
  have : CompactSpace ↥box :=
    isCompact_iff_compactSpace.mp (sequence_observableBox_isCompact R)
  have himage : IsCompact (Set.range (reconstructWeakDual coeff R hsum q hq hdom)) :=
    isCompact_range (reconstructWeakDual_continuous coeff R hsum q hq hdom)
  have hclosed : IsClosed (observableBox (fun n (ω : WeakDual ℝ E) => ω (basis n)) R) := by
    have heq : observableBox (fun n (ω : WeakDual ℝ E) => ω (basis n)) R =
        ⋂ n, {ω : WeakDual ℝ E | |ω (basis n)| ≤ R n} := by
      ext ω
      simp [observableBox]
    rw [heq]
    exact isClosed_iInter (fun n => isClosed_le (WeakDual.eval_continuous (basis n)).abs continuous_const)
  apply himage.of_isClosed_subset hclosed
  intro ω hω
  let x : ↥box := ⟨fun n => ω (basis n), hω⟩
  refine ⟨x, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  exact (hexpand ω f).symm

/-- Reconstruction compactness and coordinate tails give compact containment.
Concrete summability, continuous domination, and expansion data remain inputs. -/
theorem weakDual_compact_containment_of_tail_budget
    [MeasurableSpace (WeakDual ℝ E)]
    {ι : Type*} (μ : ι → Measure (WeakDual ℝ E))
    (basis : ℕ → E) (coeff : ℕ → E →ₗ[ℝ] ℝ) (R C : ℕ → ℝ)
    (hsum : ∀ f, Summable (fun n => |coeff n f| * R n))
    (q : Seminorm ℝ E) (hq : Continuous q)
    (hdom : ∀ f, tsum (fun n => |coeff n f| * R n) ≤ q f)
    (hexpand : ∀ (ω : WeakDual ℝ E) f,
      ω f = tsum (fun n => coeff n f * ω (basis n)))
    (hR : ∀ n, 0 < R n)
    (h_int : ∀ n i, Integrable (fun ω => ω (basis n) ^ 2) (μ i))
    (h_moment : ∀ n i, ∫ ω, ω (basis n) ^ 2 ∂(μ i) ≤ C n)
    (ε : ENNReal) (h_budget : tsum (fun n => ENNReal.ofReal (C n / R n ^ 2)) ≤ ε) :
    ∃ K : Set (WeakDual ℝ E), IsCompact K ∧ ∀ i, μ i Kᶜ ≤ ε := by
  refine ⟨observableBox (fun n ω => ω (basis n)) R,
    weakDual_coordinateBox_isCompact basis coeff R hsum q hq hdom hexpand, ?_⟩
  intro i
  exact (observableBox_compl_le μ (fun n ω => ω (basis n)) R C hR h_int h_moment i).trans h_budget


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The adjoint pairing maps a Hilbert vector to a continuous functional on the
test space. This is the continuous Riesz-type half of a configuration embedding. -/
def hilbertVectorConfiguration
    (J : E →L[ℝ] H) (x : H) : WeakDual ℝ E :=
  (innerSL ℝ x).comp J

/-- The configuration embedding is continuous for the weak-dual topology. -/
theorem hilbertVectorConfiguration_continuous (J : E →L[ℝ] H) :
    Continuous (hilbertVectorConfiguration J) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  change Continuous (fun x : H => @inner ℝ H _ x (J f))
  exact continuous_inner.comp (continuous_id.prodMk continuous_const)
end Pphi2Clean.Continuum
