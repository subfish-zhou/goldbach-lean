import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU21 : ℝ[X] := C (285270731727787/846643118400)+C (401606565373922471/507985871040000)*X^1+C (501385964618554469/761978806560000)*X^2+C (711813822454909661/3047915226240000)*X^3+C (9235906566516617/253992935520000)*X^4+C (1597365528632111/609583045248000)*X^5+C (107584810999169/1523957613120000)*X^6
def bezoutV21 : ℝ[X] := C (-401574470183083/4515429964800)+C (-276892151642832749/1015971742080000)*X^1+C (-162543215757351467/507985871040000)*X^2+C (-67998741174743977/380989403280000)*X^3+C (-588453019267187881/12191660904960000)*X^4+C (-24969535693162961/4063886968320000)*X^5+C (-4585130282075707/12191660904960000)*X^6+C (-107584810999169/12191660904960000)*X^7

theorem block21_separable : block21.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU21, bezoutV21, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU21, bezoutV21, block21, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
