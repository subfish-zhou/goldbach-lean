import SigmaActualBlockSeparable20
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator20 : ℝ[X] := C (15374879/107163)+C (4849797857/19289340)*X^1+C (1073189653/9644670)*X^2+C (49063337/19289340)*X^3

theorem residueNumerator20_degree : residueNumerator20.degree < block20.degree := by
  have hb : block20.degree = (4 : ℕ) := by
    unfold block20
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator20
  compute_degree; all_goals norm_num

def simplePartPrimitive20 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator20 block20

theorem simplePartPrimitive20_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive20 (residueNumerator20.eval t / block20.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block20_separable
    residueNumerator20_degree t (block20_eval_ne ht)

end SigmaActualBlockSeparable
