import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU11 : ℝ[X] := C (-4/17)
def bezoutV11 : ℝ[X] := C (7/17)+C (2/17)*X^1

theorem block11_separable : block11.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU11, bezoutV11, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU11, bezoutV11, block11, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
