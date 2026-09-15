import SigmaActualBlockSeparable18
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator18 : ℝ[X] := C (-35227338801530/990159920631)+C (-1303287448870/10646880867)*X^1+C (-26980325651330/330053306877)*X^2+C (-88509410/23365503)*X^3

theorem residueNumerator18_degree : residueNumerator18.degree < block18.degree := by
  have hb : block18.degree = (4 : ℕ) := by
    unfold block18
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator18
  compute_degree; all_goals norm_num

def simplePartPrimitive18 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator18 block18

theorem simplePartPrimitive18_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive18 (residueNumerator18.eval t / block18.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block18_separable
    residueNumerator18_degree t (block18_eval_ne ht)

def principalNumerator29 : ℝ[X] := C (19697447650/541959453)+C (117022016000/1625878359)*X^1+C (67674362150/1625878359)*X^2+C (8623946900/1625878359)*X^3
def principalPrimitive29 (t : ℝ) : ℝ := principalNumerator29.eval t / (block18.eval t)^1
def principalKernel29 (t : ℝ) : ℝ :=
  (principalNumerator29.derivative.eval t * block18.eval t -
    1*principalNumerator29.eval t*block18.derivative.eval t) / (block18.eval t)^2

theorem principalPrimitive29_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive29 (principalKernel29 t) t := by
  convert rationalPrimitive_deriv principalNumerator29 block18 0 t (block18_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel29]

end SigmaActualBlockSeparable
