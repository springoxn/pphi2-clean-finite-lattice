import AImathPPhi2Clean.PeriodicHMinusThreeCylinderBorelUniqueness

noncomputable section
namespace Pphi2Clean.Continuum

open MeasureTheory Topology TopologicalSpace

theorem periodicHMinusThreeCompletion_completeSpace :
    CompleteSpace PeriodicHMinusThreeCompletion := inferInstance

theorem periodicHMinusThreeCompletion_declared_borel :
    (inferInstance : MeasurableSpace PeriodicHMinusThreeCompletion) =
      borel PeriodicHMinusThreeCompletion := rfl

def periodicHMinusThreeCoordinateEmbedding :
    PeriodicHMinusThreeCompletion → PeriodicFourierIndex → ℂ :=
  fun x => (x : PeriodicFourierIndex → ℂ)

theorem continuous_periodicHMinusThreeCoordinateEmbedding :
    Continuous periodicHMinusThreeCoordinateEmbedding := by
  apply continuous_pi
  intro k
  exact continuous_periodicHMinusThree_coordinate k

theorem injective_periodicHMinusThreeCoordinateEmbedding :
    Function.Injective periodicHMinusThreeCoordinateEmbedding := by
  intro x y hxy
  apply lp.ext
  funext k
  exact congrFun hxy k

def PeriodicHMinusThreeCountableDenseInput : Prop :=
  ∃ s : Set PeriodicHMinusThreeCompletion, s.Countable ∧ Dense s

def PeriodicHMinusThreeSeparableInput : Prop :=
  SeparableSpace PeriodicHMinusThreeCompletion

def PeriodicHMinusThreeSecondCountableInput : Prop :=
  SecondCountableTopology PeriodicHMinusThreeCompletion

def PeriodicHMinusThreePolishInput : Prop :=
  PolishSpace PeriodicHMinusThreeCompletion

theorem periodicHMinusThree_separable_of_countable_dense_input
    (hdense : PeriodicHMinusThreeCountableDenseInput) :
    PeriodicHMinusThreeSeparableInput := by
  rcases hdense with ⟨s, hsc, hs⟩
  exact ⟨⟨s, hsc, hs⟩⟩

theorem periodicHMinusThree_secondCountable_of_separable_input
    (hsep : PeriodicHMinusThreeSeparableInput) :
    PeriodicHMinusThreeSecondCountableInput := by
  letI : SeparableSpace PeriodicHMinusThreeCompletion := hsep
  show SecondCountableTopology PeriodicHMinusThreeCompletion
  exact inferInstance

theorem periodicHMinusThree_polish_of_separable_input
    (hsep : PeriodicHMinusThreeSeparableInput) :
    PeriodicHMinusThreePolishInput := by
  letI : SeparableSpace PeriodicHMinusThreeCompletion := hsep
  show PolishSpace PeriodicHMinusThreeCompletion
  exact inferInstance

theorem periodicHMinusThree_coordinateEmbedding_measurableEmbedding_of_polish
    (hpolish : PeriodicHMinusThreePolishInput) :
    MeasurableEmbedding periodicHMinusThreeCoordinateEmbedding := by
  letI : PolishSpace PeriodicHMinusThreeCompletion := hpolish
  exact continuous_periodicHMinusThreeCoordinateEmbedding.measurableEmbedding
    injective_periodicHMinusThreeCoordinateEmbedding

theorem periodicHMinusThree_cylinder_sigma_eq_borel_of_polish
    (hpolish : PeriodicHMinusThreePolishInput) :
    MeasurableSpace.generateFrom periodicHMinusThreeMeasurableCylinders =
      borel PeriodicHMinusThreeCompletion := by
  letI : PolishSpace PeriodicHMinusThreeCompletion := hpolish
  letI : Countable PeriodicFourierIndex := inferInstance
  letI : SecondCountableTopology (PeriodicFourierIndex → ℂ) := inferInstance
  letI : BorelSpace (PeriodicFourierIndex → ℂ) := inferInstance
  have hemb := continuous_periodicHMinusThreeCoordinateEmbedding.measurableEmbedding
    injective_periodicHMinusThreeCoordinateEmbedding
  have hcyl : MeasurableSpace.generateFrom periodicHMinusThreeMeasurableCylinders =
      MeasurableSpace.comap periodicHMinusThreeCoordinateEmbedding
        (MeasurableSpace.pi : MeasurableSpace (PeriodicFourierIndex → ℂ)) := by
    rw [← generateFrom_measurableCylinders,
      MeasurableSpace.comap_generateFrom]
    congr 1
  calc
    MeasurableSpace.generateFrom periodicHMinusThreeMeasurableCylinders =
        MeasurableSpace.comap periodicHMinusThreeCoordinateEmbedding
          (MeasurableSpace.pi : MeasurableSpace (PeriodicFourierIndex → ℂ)) := hcyl
    _ = (inferInstance : MeasurableSpace PeriodicHMinusThreeCompletion) :=
      hemb.comap_eq
    _ = borel PeriodicHMinusThreeCompletion := rfl

theorem periodicHMinusThree_polish_of_countable_dense_input
    (hdense : PeriodicHMinusThreeCountableDenseInput) :
    PeriodicHMinusThreePolishInput :=
  periodicHMinusThree_polish_of_separable_input
    (periodicHMinusThree_separable_of_countable_dense_input hdense)

theorem periodicHMinusThree_cylinder_sigma_eq_borel_of_countable_dense_input
    (hdense : PeriodicHMinusThreeCountableDenseInput) :
    MeasurableSpace.generateFrom periodicHMinusThreeMeasurableCylinders =
      borel PeriodicHMinusThreeCompletion :=
  periodicHMinusThree_cylinder_sigma_eq_borel_of_polish
    (periodicHMinusThree_polish_of_countable_dense_input hdense)

/-- The concrete `lp` carrier is separable: finite-coordinate truncations
converge in norm, and finite linear combinations of the coordinate vectors
form a separable dense subspace. -/
theorem periodicHMinusThreeCompletion_separable :
    TopologicalSpace.SeparableSpace PeriodicHMinusThreeCompletion := by
  classical
  let S : Set PeriodicHMinusThreeCompletion := Set.range
    (fun k : PeriodicFourierIndex =>
      lp.single (E := fun _ : PeriodicFourierIndex => ℂ) 2 k (1 : ℂ))
  have hS : IsSeparable S := (Set.countable_range _).isSeparable
  have hspan : IsSeparable (Submodule.span ℂ S : Set PeriodicHMinusThreeCompletion) :=
    TopologicalSpace.IsSeparable.span hS
  have hdense : Dense (Submodule.span ℂ S : Set PeriodicHMinusThreeCompletion) := by
    rw [Metric.dense_iff]
    intro x ε hε
    let F : Finset PeriodicFourierIndex → PeriodicHMinusThreeCompletion :=
      fun s => ∑ i ∈ s, lp.single 2 i (x i)
    have hs : HasSum
        (fun i : PeriodicFourierIndex => lp.single 2 i (x i)) x :=
      lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) x
    rw [HasSum, Metric.tendsto_nhds] at hs
    have hev := hs ε hε
    obtain ⟨s, hs⟩ := hev.exists
    refine ⟨F s, ?_⟩
    constructor
    · simpa [Metric.mem_ball, F] using hs
    · apply Submodule.sum_mem
      intro i hi
      have hterm : lp.single (E := fun _ : PeriodicFourierIndex => ℂ) 2 i (x i) =
          x i • lp.single (E := fun _ : PeriodicFourierIndex => ℂ) 2 i (1 : ℂ) := by
        simpa using (lp.single_smul
          (E := fun _ : PeriodicFourierIndex => ℂ) (p := (2 : ENNReal))
          i (x i) (1 : ℂ))
      rw [hterm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact hdense.isSeparable_iff.mp hspan

end Pphi2Clean.Continuum
