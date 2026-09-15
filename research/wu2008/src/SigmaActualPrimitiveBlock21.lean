import SigmaActualBlockSeparable21
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator21 : ℝ[X] := C (42812698288000000/23602032098001)+C (540164332952750000/23602032098001)*X^1+C (3924870142694500000/70806096294003)*X^2+C (1263145012827875000/23602032098001)*X^3+C (1589927943510500000/70806096294003)*X^4+C (254132667434000000/70806096294003)*X^5+C (5607688132000000/23602032098001)*X^6+C (375958559125000/70806096294003)*X^7

theorem residueNumerator21_degree : residueNumerator21.degree < block21.degree := by
  have hb : block21.degree = (8 : ℕ) := by
    unfold block21
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator21
  compute_degree; all_goals norm_num

def simplePartPrimitive21 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator21 block21

theorem simplePartPrimitive21_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive21 (residueNumerator21.eval t / block21.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block21_separable
    residueNumerator21_degree t (block21_eval_ne ht)

end SigmaActualBlockSeparable
