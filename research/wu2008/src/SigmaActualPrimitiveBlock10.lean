import SigmaActualBlockSeparable10
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator10 : ℝ[X] := C ((-929708336108082900646028333590/154426641069417257499442892038323)+(-239096765944848576385172952506/154426641069417257499442892038323)*TerminalE.radical)+C ((44295915602693330213306071490/51475547023139085833147630679441)+(106209019136768585745254738036/463279923208251772498328676114969)*TerminalE.radical)*X^1

theorem residueNumerator10_degree : residueNumerator10.degree < block10.degree := by
  have hb : block10.degree = (2 : ℕ) := by
    unfold block10
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator10
  compute_degree; all_goals norm_num

def simplePartPrimitive10 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator10 block10

theorem simplePartPrimitive10_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive10 (residueNumerator10.eval t / block10.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block10_separable
    residueNumerator10_degree t (block10_eval_ne ht)

end SigmaActualBlockSeparable
