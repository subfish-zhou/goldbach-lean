import SigmaActualBlockSeparable7
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator7 : ℝ[X] := C ((-169054480550/40270319397)+(19261450400/40270319397)*TerminalE.radical)

theorem residueNumerator7_degree : residueNumerator7.degree < block7.degree := by
  have hb : block7.degree = (1 : ℕ) := by
    unfold block7
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator7
  compute_degree; all_goals norm_num

def simplePartPrimitive7 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator7 block7

theorem simplePartPrimitive7_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive7 (residueNumerator7.eval t / block7.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block7_separable
    residueNumerator7_degree t (block7_eval_ne ht)

def principalNumerator14 : ℝ[X] := C ((2684485000/174330387)+(-232519450/58110129)*TerminalE.radical)
def principalPrimitive14 (t : ℝ) : ℝ := principalNumerator14.eval t / (block7.eval t)^1
def principalKernel14 (t : ℝ) : ℝ :=
  (principalNumerator14.derivative.eval t * block7.eval t -
    1*principalNumerator14.eval t*block7.derivative.eval t) / (block7.eval t)^2

theorem principalPrimitive14_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive14 (principalKernel14 t) t := by
  convert rationalPrimitive_deriv principalNumerator14 block7 0 t (block7_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel14]

end SigmaActualBlockSeparable
