import AImathPPhi2Clean.PeriodicFS4DCompactEmbedding
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

noncomputable section
namespace Pphi2Clean.Continuum

abbrev Periodic3DIndex := Fin 3 → ℤ

def periodic3DExtend (k : Periodic3DIndex) : FS4Index :=
  fun i => if h : i.val < 3 then k ⟨i.val, h⟩ else 0

theorem periodic3DExtend_injective : Function.Injective periodic3DExtend := by
  intro k l h
  funext i
  have hi : (⟨i.val, Nat.lt_trans i.isLt (by decide : 3 < 4)⟩ : Fin 4).val < 3 := by
    simpa using i.isLt
  have hval := congrFun h (⟨i.val, Nat.lt_trans i.isLt (by decide : 3 < 4)⟩ : Fin 4)
  simpa [periodic3DExtend, hi] using hval

def periodic3DSobolevWeight (s : ℝ) (k : Periodic3DIndex) : ℝ :=
  fs4SobolevWeight s (periodic3DExtend k)

def periodic3DHminusThreeWeight (k : Periodic3DIndex) : ℝ := periodic3DSobolevWeight 3 k
def periodic3DHminusFourWeight (k : Periodic3DIndex) : ℝ := periodic3DSobolevWeight 4 k

theorem periodic3DSobolevWeight_nonneg (s : ℝ) (k : Periodic3DIndex) :
    0 ≤ periodic3DSobolevWeight s k := fs4SobolevWeight_nonneg s _

theorem periodic3DSobolevWeight_summable (s : ℝ) (hs : 2 < s) :
    Summable (periodic3DSobolevWeight s) := by
  exact (fs4SobolevWeight_summable s hs).comp_injective periodic3DExtend_injective

theorem periodic3DHminusThreeWeight_summable :
    Summable periodic3DHminusThreeWeight := periodic3DSobolevWeight_summable 3 (by norm_num)

theorem periodic3DHminusFourWeight_summable :
    Summable periodic3DHminusFourWeight := periodic3DSobolevWeight_summable 4 (by norm_num)

theorem periodic3DHminusFourWeight_le_three (k : Periodic3DIndex) :
    periodic3DHminusFourWeight k ≤ periodic3DHminusThreeWeight k :=
  fs4_weight_four_le_three (periodic3DExtend k)

end Pphi2Clean.Continuum
