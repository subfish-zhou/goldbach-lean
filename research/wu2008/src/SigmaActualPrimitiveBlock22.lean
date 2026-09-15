import SigmaActualBlockSeparable22
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator22 : ℝ[X] := C (70444099961000000/288027314883)+C (2855563984093750000/2592245833947)*X^1+C (4767798523888000000/2592245833947)*X^2+C (975725433519875000/706976136531)*X^3+C (3316346357490500000/7776737501841)*X^4+C (77158806247000000/2592245833947)*X^5+C (787418630500000/706976136531)*X^6+C (190652822125000/7776737501841)*X^7

theorem residueNumerator22_degree : residueNumerator22.degree < block22.degree := by
  have hb : block22.degree = (8 : ℕ) := by
    unfold block22
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator22
  compute_degree; all_goals norm_num

def simplePartPrimitive22 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator22 block22

theorem simplePartPrimitive22_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive22 (residueNumerator22.eval t / block22.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block22_separable
    residueNumerator22_degree t (block22_eval_ne ht)

end SigmaActualBlockSeparable
