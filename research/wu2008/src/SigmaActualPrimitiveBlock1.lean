import SigmaActualBlockSeparable1
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator1 : ℝ[X] := C (15264954499/29767500000)

theorem residueNumerator1_degree : residueNumerator1.degree < block1.degree := by
  have hb : block1.degree = (1 : ℕ) := by
    unfold block1
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator1
  compute_degree; all_goals norm_num

def simplePartPrimitive1 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator1 block1

theorem simplePartPrimitive1_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive1 (residueNumerator1.eval t / block1.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block1_separable
    residueNumerator1_degree t (block1_eval_ne ht)

def principalNumerator0 : ℝ[X] := C (5190821/141750000)
def principalPrimitive0 (t : ℝ) : ℝ := principalNumerator0.eval t / (block1.eval t)^1
def principalKernel0 (t : ℝ) : ℝ :=
  (principalNumerator0.derivative.eval t * block1.eval t -
    1*principalNumerator0.eval t*block1.derivative.eval t) / (block1.eval t)^2

theorem principalPrimitive0_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive0 (principalKernel0 t) t := by
  convert rationalPrimitive_deriv principalNumerator0 block1 0 t (block1_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel0]

end SigmaActualBlockSeparable
