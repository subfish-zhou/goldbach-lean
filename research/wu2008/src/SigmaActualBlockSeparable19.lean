import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU19 : ℝ[X] := C (7792315/25043562)+C (21587573/751306860)*X^1+C (698023/375653430)*X^2
def bezoutV19 : ℝ[X] := C (-7854701/50087124)+C (-10041341/62608905)*X^1+C (-14632913/1502613720)*X^2+C (-698023/1502613720)*X^3

theorem block19_separable : block19.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU19, bezoutV19, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU19, bezoutV19, block19, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
