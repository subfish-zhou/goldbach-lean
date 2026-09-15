import SigmaActualBlockSeparable14
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator14 : ℝ[X] := C ((15187127927552281000000/372417960487462127469)+(3088339519064584000000/372417960487462127469)*TerminalE.radical)+C ((13974047285837000000/1991539895654877687)+(2343254407016000000/5974619686964633061)*TerminalE.radical)*X^1

theorem residueNumerator14_degree : residueNumerator14.degree < block14.degree := by
  have hb : block14.degree = (2 : ℕ) := by
    unfold block14
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator14
  compute_degree; all_goals norm_num

def simplePartPrimitive14 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator14 block14

theorem simplePartPrimitive14_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive14 (residueNumerator14.eval t / block14.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block14_separable
    residueNumerator14_degree t (block14_eval_ne ht)

end SigmaActualBlockSeparable
