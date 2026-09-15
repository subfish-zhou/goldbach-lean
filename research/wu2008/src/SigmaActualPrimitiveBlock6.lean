import SigmaActualBlockSeparable6
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator6 : ℝ[X] := C (-110247/28000)

theorem residueNumerator6_degree : residueNumerator6.degree < block6.degree := by
  have hb : block6.degree = (1 : ℕ) := by
    unfold block6
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator6
  compute_degree; all_goals norm_num

def simplePartPrimitive6 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator6 block6

theorem simplePartPrimitive6_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive6 (residueNumerator6.eval t / block6.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block6_separable
    residueNumerator6_degree t (block6_eval_ne ht)

def principalNumerator13 : ℝ[X] := C (-20289/19600)
def principalPrimitive13 (t : ℝ) : ℝ := principalNumerator13.eval t / (block6.eval t)^1
def principalKernel13 (t : ℝ) : ℝ :=
  (principalNumerator13.derivative.eval t * block6.eval t -
    1*principalNumerator13.eval t*block6.derivative.eval t) / (block6.eval t)^2

theorem principalPrimitive13_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive13 (principalKernel13 t) t := by
  convert rationalPrimitive_deriv principalNumerator13 block6 0 t (block6_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel13]

end SigmaActualBlockSeparable
