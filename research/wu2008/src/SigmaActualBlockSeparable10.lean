import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU10 : ℝ[X] := C (-1/15)
def bezoutV10 : ℝ[X] := C (-1/10)+C (1/30)*X^1

theorem block10_separable : block10.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU10, bezoutV10, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU10, bezoutV10, block10, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
