import SigmaActualBlockSeparable4
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator4 : ℝ[X] := C ((283368648799027705009269493043200/290647201319777664296743488491889)+(-4551523047275320836690259456000/290647201319777664296743488491889)*TerminalE.radical)

theorem residueNumerator4_degree : residueNumerator4.degree < block4.degree := by
  have hb : block4.degree = (1 : ℕ) := by
    unfold block4
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator4
  compute_degree; all_goals norm_num

def simplePartPrimitive4 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator4 block4

theorem simplePartPrimitive4_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive4 (residueNumerator4.eval t / block4.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block4_separable
    residueNumerator4_degree t (block4_eval_ne ht)

def principalNumerator7 : ℝ[X] := C ((-11363620589124323686638592000/5106140099390612078267901507)+(3257643376802687477419110400/5106140099390612078267901507)*TerminalE.radical)
def principalPrimitive7 (t : ℝ) : ℝ := principalNumerator7.eval t / (block4.eval t)^1
def principalKernel7 (t : ℝ) : ℝ :=
  (principalNumerator7.derivative.eval t * block4.eval t -
    1*principalNumerator7.eval t*block4.derivative.eval t) / (block4.eval t)^2

theorem principalPrimitive7_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive7 (principalKernel7 t) t := by
  convert rationalPrimitive_deriv principalNumerator7 block4 0 t (block4_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel7]

def principalNumerator8 : ℝ[X] := C ((162003511199503628288000/89705548844831087532441)+(-4504290509963970560000/9967283204981231948049)*TerminalE.radical)
def principalPrimitive8 (t : ℝ) : ℝ := principalNumerator8.eval t / (block4.eval t)^2
def principalKernel8 (t : ℝ) : ℝ :=
  (principalNumerator8.derivative.eval t * block4.eval t -
    2*principalNumerator8.eval t*block4.derivative.eval t) / (block4.eval t)^3

theorem principalPrimitive8_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive8 (principalKernel8 t) t := by
  exact rationalPrimitive_deriv principalNumerator8 block4 1 t (block4_eval_ne ht)

def principalNumerator9 : ℝ[X] := C ((-2364007120732160000/4727887604090268849)+(22794067419136000/175106948299639587)*TerminalE.radical)
def principalPrimitive9 (t : ℝ) : ℝ := principalNumerator9.eval t / (block4.eval t)^3
def principalKernel9 (t : ℝ) : ℝ :=
  (principalNumerator9.derivative.eval t * block4.eval t -
    3*principalNumerator9.eval t*block4.derivative.eval t) / (block4.eval t)^4

theorem principalPrimitive9_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive9 (principalKernel9 t) t := by
  exact rationalPrimitive_deriv principalNumerator9 block4 2 t (block4_eval_ne ht)

end SigmaActualBlockSeparable
