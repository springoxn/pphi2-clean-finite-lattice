import AImathPPhi2Clean.PhysicalLatticeGaussianLaw
import AImathPPhi2Clean.ContinuumProbability
noncomputable section
namespace Pphi2Clean.Continuum
open MeasureTheory ProbabilityTheory
def physicalFamilyEvalMap (d N m : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ) →
      EuclideanSpace ℝ (Fin m) :=
  fun ω => WithLp.toLp 2 (fun j => ω (fs j))
def physicalFamilyEvalMeasure (d N m : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  Measure.map (physicalFamilyEvalMap d N m a mass ha hmass fs)
    (physicalGJMeasure d N a mass ha hmass)
instance physicalFamilyEvalMeasure_probability (d N m : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    IsProbabilityMeasure (physicalFamilyEvalMeasure d N m a mass ha hmass fs) := by
  unfold physicalFamilyEvalMeasure
  apply map_preserves_probability
  exact (physicalGJMeasure_family_hasGaussianLaw d N a mass ha hmass fs).aemeasurable
def physicalFamilyEvalProbabilityMeasure (d N m : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) :=
  ⟨physicalFamilyEvalMeasure d N m a mass ha hmass fs, inferInstance⟩
@[simp] theorem physicalFamilyEvalMap_apply (d N m : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ)) (j : Fin m) :
    (physicalFamilyEvalMap d N m a mass ha hmass fs ω) j = ω (fs j) := by
  simp [physicalFamilyEvalMap]
theorem physicalFamilyEvalMeasure_hasGaussianLaw (d N m : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ) :
    HasGaussianLaw (physicalFamilyEvalMap d N m a mass ha hmass fs)
      (physicalGJMeasure d N a mass ha hmass) := by
  exact physicalGJMeasure_family_hasGaussianLaw d N a mass ha hmass fs
theorem physicalFamilyEvalMeasure_covariance_entry (d N m : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (i j : Fin m) :
    ∫ z : EuclideanSpace ℝ (Fin m), z i * z j ∂
      physicalFamilyEvalMeasure d N m a mass ha hmass fs =
      ∫ ω : WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ),
        ω (fs i) * ω (fs j) ∂physicalGJMeasure d N a mass ha hmass := by
  unfold physicalFamilyEvalMeasure physicalFamilyEvalMap
  have hmeas := (physicalGJMeasure_family_hasGaussianLaw d N a mass ha hmass fs).aemeasurable
  have hcoord_i : Measurable (fun z : EuclideanSpace ℝ (Fin m) => z i) :=
    ((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ))).measurable
  have hcoord_j : Measurable (fun z : EuclideanSpace ℝ (Fin m) => z j) :=
    ((continuous_apply j).comp (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ))).measurable
  have hprod : Measurable (fun z : EuclideanSpace ℝ (Fin m) => z i * z j) :=
    hcoord_i.mul hcoord_j
  rw [integral_map hmeas hprod.aestronglyMeasurable]
end Pphi2Clean.Continuum
