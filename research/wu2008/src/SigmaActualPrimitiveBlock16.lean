import SigmaActualBlockSeparable16
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator16 : ℝ[X] := C (6562789/750141)+C (21810826/1607445)*X^1+C (9723493/1607445)*X^2+C (6835852/11252115)*X^3

theorem residueNumerator16_degree : residueNumerator16.degree < block16.degree := by
  have hb : block16.degree = (4 : ℕ) := by
    unfold block16
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator16
  compute_degree; all_goals norm_num

def simplePartPrimitive16 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator16 block16

theorem simplePartPrimitive16_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive16 (residueNumerator16.eval t / block16.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block16_separable
    residueNumerator16_degree t (block16_eval_ne ht)

end SigmaActualBlockSeparable
