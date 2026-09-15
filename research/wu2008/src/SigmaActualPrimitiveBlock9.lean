import SigmaActualBlockSeparable9
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator9 : ℝ[X] := C (-23145358416/1143828125)

theorem residueNumerator9_degree : residueNumerator9.degree < block9.degree := by
  have hb : block9.degree = (1 : ℕ) := by
    unfold block9
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator9
  compute_degree; all_goals norm_num

def simplePartPrimitive9 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator9 block9

theorem simplePartPrimitive9_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive9 (residueNumerator9.eval t / block9.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block9_separable
    residueNumerator9_degree t (block9_eval_ne ht)

def principalNumerator16 : ℝ[X] := C (-114455383104/1019046875)
def principalPrimitive16 (t : ℝ) : ℝ := principalNumerator16.eval t / (block9.eval t)^1
def principalKernel16 (t : ℝ) : ℝ :=
  (principalNumerator16.derivative.eval t * block9.eval t -
    1*principalNumerator16.eval t*block9.derivative.eval t) / (block9.eval t)^2

theorem principalPrimitive16_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive16 (principalKernel16 t) t := by
  convert rationalPrimitive_deriv principalNumerator16 block9 0 t (block9_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel16]

def principalNumerator17 : ℝ[X] := C (7176459264/18528125)
def principalPrimitive17 (t : ℝ) : ℝ := principalNumerator17.eval t / (block9.eval t)^2
def principalKernel17 (t : ℝ) : ℝ :=
  (principalNumerator17.derivative.eval t * block9.eval t -
    2*principalNumerator17.eval t*block9.derivative.eval t) / (block9.eval t)^3

theorem principalPrimitive17_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive17 (principalKernel17 t) t := by
  exact rationalPrimitive_deriv principalNumerator17 block9 1 t (block9_eval_ne ht)

def principalNumerator18 : ℝ[X] := C (-35091072/48125)
def principalPrimitive18 (t : ℝ) : ℝ := principalNumerator18.eval t / (block9.eval t)^3
def principalKernel18 (t : ℝ) : ℝ :=
  (principalNumerator18.derivative.eval t * block9.eval t -
    3*principalNumerator18.eval t*block9.derivative.eval t) / (block9.eval t)^4

theorem principalPrimitive18_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive18 (principalKernel18 t) t := by
  exact rationalPrimitive_deriv principalNumerator18 block9 2 t (block9_eval_ne ht)

end SigmaActualBlockSeparable
