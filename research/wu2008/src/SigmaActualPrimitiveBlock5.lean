import SigmaActualBlockSeparable5
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator5 : ℝ[X] := C ((359112744240400958043733712384000/290647201319777664296743488491889)+(4167200998603768189767899648000/32294133479975296032971498721321)*TerminalE.radical)

theorem residueNumerator5_degree : residueNumerator5.degree < block5.degree := by
  have hb : block5.degree = (1 : ℕ) := by
    unfold block5
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator5
  compute_degree; all_goals norm_num

def simplePartPrimitive5 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator5 block5

theorem simplePartPrimitive5_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive5 (residueNumerator5.eval t / block5.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block5_separable
    residueNumerator5_degree t (block5_eval_ne ht)

def principalNumerator10 : ℝ[X] := C ((2943470402352542207398912000/5106140099390612078267901507)+(1286446725059766562102784000/5106140099390612078267901507)*TerminalE.radical)
def principalPrimitive10 (t : ℝ) : ℝ := principalNumerator10.eval t / (block5.eval t)^1
def principalKernel10 (t : ℝ) : ℝ :=
  (principalNumerator10.derivative.eval t * block5.eval t -
    1*principalNumerator10.eval t*block5.derivative.eval t) / (block5.eval t)^2

theorem principalPrimitive10_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive10 (principalKernel10 t) t := by
  convert rationalPrimitive_deriv principalNumerator10 block5 0 t (block5_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel10]

def principalNumerator11 : ℝ[X] := C ((105473794639166777344000/89705548844831087532441)+(25663584480380254208000/89705548844831087532441)*TerminalE.radical)
def principalPrimitive11 (t : ℝ) : ℝ := principalNumerator11.eval t / (block5.eval t)^2
def principalKernel11 (t : ℝ) : ℝ :=
  (principalNumerator11.derivative.eval t * block5.eval t -
    2*principalNumerator11.eval t*block5.derivative.eval t) / (block5.eval t)^3

theorem principalPrimitive11_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive11 (principalKernel11 t) t := by
  exact rationalPrimitive_deriv principalNumerator11 block5 1 t (block5_eval_ne ht)

def principalNumerator12 : ℝ[X] := C ((2364007120732160000/4727887604090268849)+(22794067419136000/175106948299639587)*TerminalE.radical)
def principalPrimitive12 (t : ℝ) : ℝ := principalNumerator12.eval t / (block5.eval t)^3
def principalKernel12 (t : ℝ) : ℝ :=
  (principalNumerator12.derivative.eval t * block5.eval t -
    3*principalNumerator12.eval t*block5.derivative.eval t) / (block5.eval t)^4

theorem principalPrimitive12_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive12 (principalKernel12 t) t := by
  exact rationalPrimitive_deriv principalNumerator12 block5 2 t (block5_eval_ne ht)

end SigmaActualBlockSeparable
