import SigmaActualBlockSeparable12
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator12 : ℝ[X] := C (-19515919/34768440)+C (-969637/2381400)*X^1

theorem residueNumerator12_degree : residueNumerator12.degree < block12.degree := by
  have hb : block12.degree = (2 : ℕ) := by
    unfold block12
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator12
  compute_degree; all_goals norm_num

def simplePartPrimitive12 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator12 block12

theorem simplePartPrimitive12_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive12 (residueNumerator12.eval t / block12.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block12_separable
    residueNumerator12_degree t (block12_eval_ne ht)

def principalNumerator22 : ℝ[X] := C (-6513937/18625950)+C (-5323127/18625950)*X^1
def principalPrimitive22 (t : ℝ) : ℝ := principalNumerator22.eval t / (block12.eval t)^1
def principalKernel22 (t : ℝ) : ℝ :=
  (principalNumerator22.derivative.eval t * block12.eval t -
    1*principalNumerator22.eval t*block12.derivative.eval t) / (block12.eval t)^2

theorem principalPrimitive22_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive22 (principalKernel22 t) t := by
  convert rationalPrimitive_deriv principalNumerator22 block12 0 t (block12_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel22]

end SigmaActualBlockSeparable
