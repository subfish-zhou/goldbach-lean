import SigmaActualBlockSeparable3
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator3 : ℝ[X] := C ((-537614752/56260575)+(-608/27783)*TerminalE.radical)

theorem residueNumerator3_degree : residueNumerator3.degree < block3.degree := by
  have hb : block3.degree = (1 : ℕ) := by
    unfold block3
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator3
  compute_degree; all_goals norm_num

def simplePartPrimitive3 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator3 block3

theorem simplePartPrimitive3_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive3 (residueNumerator3.eval t / block3.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block3_separable
    residueNumerator3_degree t (block3_eval_ne ht)

def principalNumerator4 : ℝ[X] := C ((-983296/535815)+(-1504/11907)*TerminalE.radical)
def principalPrimitive4 (t : ℝ) : ℝ := principalNumerator4.eval t / (block3.eval t)^1
def principalKernel4 (t : ℝ) : ℝ :=
  (principalNumerator4.derivative.eval t * block3.eval t -
    1*principalNumerator4.eval t*block3.derivative.eval t) / (block3.eval t)^2

theorem principalPrimitive4_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive4 (principalKernel4 t) t := by
  convert rationalPrimitive_deriv principalNumerator4 block3 0 t (block3_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel4]

def principalNumerator5 : ℝ[X] := C (950144/893025)
def principalPrimitive5 (t : ℝ) : ℝ := principalNumerator5.eval t / (block3.eval t)^2
def principalKernel5 (t : ℝ) : ℝ :=
  (principalNumerator5.derivative.eval t * block3.eval t -
    2*principalNumerator5.eval t*block3.derivative.eval t) / (block3.eval t)^3

theorem principalPrimitive5_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive5 (principalKernel5 t) t := by
  exact rationalPrimitive_deriv principalNumerator5 block3 1 t (block3_eval_ne ht)

def principalNumerator6 : ℝ[X] := C (-355456/893025)
def principalPrimitive6 (t : ℝ) : ℝ := principalNumerator6.eval t / (block3.eval t)^3
def principalKernel6 (t : ℝ) : ℝ :=
  (principalNumerator6.derivative.eval t * block3.eval t -
    3*principalNumerator6.eval t*block3.derivative.eval t) / (block3.eval t)^4

theorem principalPrimitive6_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive6 (principalKernel6 t) t := by
  exact rationalPrimitive_deriv principalNumerator6 block3 2 t (block3_eval_ne ht)

end SigmaActualBlockSeparable
