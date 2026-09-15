import SigmaActualBlockSeparable17
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator17 : ℝ[X] := C (3017516040456199944180140768000/132522138904946305504631683041)+C (2920516964960575112957146304000/56795202387834130930556435589)*X^1+C (10812002320536383306741614880000/397566416714838916513895049123)*X^2+C (14496797585002240000/13255189219635693561)*X^3

theorem residueNumerator17_degree : residueNumerator17.degree < block17.degree := by
  have hb : block17.degree = (4 : ℕ) := by
    unfold block17
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator17
  compute_degree; all_goals norm_num

def simplePartPrimitive17 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator17 block17

theorem simplePartPrimitive17_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive17 (residueNumerator17.eval t / block17.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block17_separable
    residueNumerator17_degree t (block17_eval_ne ht)

def principalNumerator26 : ℝ[X] := C (-18757976132652539097779897600/90582459948698773413965607)+C (266367417495321772652953600/1848621631606097416611543)*X^1+C (3681816476772317354806240000/90582459948698773413965607)*X^2+C (22501140074683809863820800/10064717772077641490440623)*X^3
def principalPrimitive26 (t : ℝ) : ℝ := principalNumerator26.eval t / (block17.eval t)^1
def principalKernel26 (t : ℝ) : ℝ :=
  (principalNumerator26.derivative.eval t * block17.eval t -
    1*principalNumerator26.eval t*block17.derivative.eval t) / (block17.eval t)^2

theorem principalPrimitive26_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive26 (principalKernel26 t) t := by
  convert rationalPrimitive_deriv principalNumerator26 block17 0 t (block17_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel26]

def principalNumerator27 : ℝ[X] := C (-852678298600614434048000/6642587387559132009)+C (64658357125178266496000/948941055365590287)*X^1+C (176774970743892497920000/6642587387559132009)*X^2+C (18564554220480404096000/6642587387559132009)*X^3
def principalPrimitive27 (t : ℝ) : ℝ := principalNumerator27.eval t / (block17.eval t)^2
def principalKernel27 (t : ℝ) : ℝ :=
  (principalNumerator27.derivative.eval t * block17.eval t -
    2*principalNumerator27.eval t*block17.derivative.eval t) / (block17.eval t)^3

theorem principalPrimitive27_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive27 (principalKernel27 t) t := by
  exact rationalPrimitive_deriv principalNumerator27 block17 1 t (block17_eval_ne ht)

def principalNumerator28 : ℝ[X] := C (26585663353054720000/1461341430549)+C (36438170467840000/1104566463)*X^1+C (2857392521075200000/162371270061)*X^2+C (3077700661429760000/1461341430549)*X^3
def principalPrimitive28 (t : ℝ) : ℝ := principalNumerator28.eval t / (block17.eval t)^3
def principalKernel28 (t : ℝ) : ℝ :=
  (principalNumerator28.derivative.eval t * block17.eval t -
    3*principalNumerator28.eval t*block17.derivative.eval t) / (block17.eval t)^4

theorem principalPrimitive28_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive28 (principalKernel28 t) t := by
  exact rationalPrimitive_deriv principalNumerator28 block17 2 t (block17_eval_ne ht)

end SigmaActualBlockSeparable
