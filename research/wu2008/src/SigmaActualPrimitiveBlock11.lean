import SigmaActualBlockSeparable11
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator11 : ℝ[X] := C (7571714713/38681031600)+C (46746967/385786800)*X^1

theorem residueNumerator11_degree : residueNumerator11.degree < block11.degree := by
  have hb : block11.degree = (2 : ℕ) := by
    unfold block11
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator11
  compute_degree; all_goals norm_num

def simplePartPrimitive11 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator11 block11

theorem simplePartPrimitive11_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive11 (residueNumerator11.eval t / block11.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block11_separable
    residueNumerator11_degree t (block11_eval_ne ht)

def principalNumerator19 : ℝ[X] := C (2527043705/9476852742)+C (1032395153/8774863650)*X^1
def principalPrimitive19 (t : ℝ) : ℝ := principalNumerator19.eval t / (block11.eval t)^1
def principalKernel19 (t : ℝ) : ℝ :=
  (principalNumerator19.derivative.eval t * block11.eval t -
    1*principalNumerator19.eval t*block11.derivative.eval t) / (block11.eval t)^2

theorem principalPrimitive19_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive19 (principalKernel19 t) t := by
  convert rationalPrimitive_deriv principalNumerator19 block11 0 t (block11_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel19]

def principalNumerator20 : ℝ[X] := C (-4504313242/6968274075)+C (-53150086/142209675)*X^1
def principalPrimitive20 (t : ℝ) : ℝ := principalNumerator20.eval t / (block11.eval t)^2
def principalKernel20 (t : ℝ) : ℝ :=
  (principalNumerator20.derivative.eval t * block11.eval t -
    2*principalNumerator20.eval t*block11.derivative.eval t) / (block11.eval t)^3

theorem principalPrimitive20_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive20 (principalKernel20 t) t := by
  exact rationalPrimitive_deriv principalNumerator20 block11 1 t (block11_eval_ne ht)

def principalNumerator21 : ℝ[X] := C (22708768/35134155)+C (184188896/409898475)*X^1
def principalPrimitive21 (t : ℝ) : ℝ := principalNumerator21.eval t / (block11.eval t)^3
def principalKernel21 (t : ℝ) : ℝ :=
  (principalNumerator21.derivative.eval t * block11.eval t -
    3*principalNumerator21.eval t*block11.derivative.eval t) / (block11.eval t)^4

theorem principalPrimitive21_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive21 (principalKernel21 t) t := by
  exact rationalPrimitive_deriv principalNumerator21 block11 2 t (block11_eval_ne ht)

end SigmaActualBlockSeparable
