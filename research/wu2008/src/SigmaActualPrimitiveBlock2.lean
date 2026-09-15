import SigmaActualBlockSeparable2
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator2 : ℝ[X] := C (-6172664488/1775587275)

theorem residueNumerator2_degree : residueNumerator2.degree < block2.degree := by
  have hb : block2.degree = (1 : ℕ) := by
    unfold block2
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator2
  compute_degree; all_goals norm_num

def simplePartPrimitive2 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator2 block2

theorem simplePartPrimitive2_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive2 (residueNumerator2.eval t / block2.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block2_separable
    residueNumerator2_degree t (block2_eval_ne ht)

def principalNumerator1 : ℝ[X] := C (-18550849/2928200)
def principalPrimitive1 (t : ℝ) : ℝ := principalNumerator1.eval t / (block2.eval t)^1
def principalKernel1 (t : ℝ) : ℝ :=
  (principalNumerator1.derivative.eval t * block2.eval t -
    1*principalNumerator1.eval t*block2.derivative.eval t) / (block2.eval t)^2

theorem principalPrimitive1_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive1 (principalKernel1 t) t := by
  convert rationalPrimitive_deriv principalNumerator1 block2 0 t (block2_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel1]

def principalNumerator2 : ℝ[X] := C (54125/74536)
def principalPrimitive2 (t : ℝ) : ℝ := principalNumerator2.eval t / (block2.eval t)^2
def principalKernel2 (t : ℝ) : ℝ :=
  (principalNumerator2.derivative.eval t * block2.eval t -
    2*principalNumerator2.eval t*block2.derivative.eval t) / (block2.eval t)^3

theorem principalPrimitive2_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive2 (principalKernel2 t) t := by
  exact rationalPrimitive_deriv principalNumerator2 block2 1 t (block2_eval_ne ht)

def principalNumerator3 : ℝ[X] := C (-375/847)
def principalPrimitive3 (t : ℝ) : ℝ := principalNumerator3.eval t / (block2.eval t)^3
def principalKernel3 (t : ℝ) : ℝ :=
  (principalNumerator3.derivative.eval t * block2.eval t -
    3*principalNumerator3.eval t*block2.derivative.eval t) / (block2.eval t)^4

theorem principalPrimitive3_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive3 (principalKernel3 t) t := by
  exact rationalPrimitive_deriv principalNumerator3 block2 2 t (block2_eval_ne ht)

end SigmaActualBlockSeparable
