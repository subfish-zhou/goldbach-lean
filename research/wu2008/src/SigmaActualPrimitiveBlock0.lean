import SigmaActualBlockSeparable0
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator0 : ℝ[X] := C ((107936200890538697526045961497892472303/733152806400247720882616431269684702000)+(-6389132/146349451076787)*TerminalE.radical)

theorem residueNumerator0_degree : residueNumerator0.degree < block0.degree := by
  have hb : block0.degree = (1 : ℕ) := by
    unfold block0
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator0
  compute_degree; all_goals norm_num

def simplePartPrimitive0 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator0 block0

theorem simplePartPrimitive0_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive0 (residueNumerator0.eval t / block0.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block0_separable
    residueNumerator0_degree t (block0_eval_ne ht)

end SigmaActualBlockSeparable
