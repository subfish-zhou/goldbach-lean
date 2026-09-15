import SigmaActualBlockSeparable8
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator8 : ℝ[X] := C ((-29771278750/1181901913731)+(683726383400/3545705741193)*TerminalE.radical)

theorem residueNumerator8_degree : residueNumerator8.degree < block8.degree := by
  have hb : block8.degree = (1 : ℕ) := by
    unfold block8
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator8
  compute_degree; all_goals norm_num

def simplePartPrimitive8 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator8 block8

theorem simplePartPrimitive8_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive8 (residueNumerator8.eval t / block8.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block8_separable
    residueNumerator8_degree t (block8_eval_ne ht)

def principalNumerator15 : ℝ[X] := C ((-59834000/832911849)+(-13177750/832911849)*TerminalE.radical)
def principalPrimitive15 (t : ℝ) : ℝ := principalNumerator15.eval t / (block8.eval t)^1
def principalKernel15 (t : ℝ) : ℝ :=
  (principalNumerator15.derivative.eval t * block8.eval t -
    1*principalNumerator15.eval t*block8.derivative.eval t) / (block8.eval t)^2

theorem principalPrimitive15_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive15 (principalKernel15 t) t := by
  convert rationalPrimitive_deriv principalNumerator15 block8 0 t (block8_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel15]

end SigmaActualBlockSeparable
