import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU15 : ℝ[X] := C (-4/433)
def bezoutV15 : ℝ[X] := C (23/433)+C (2/433)*X^1

theorem block15_separable : block15.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU15, bezoutV15, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU15, bezoutV15, block15, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
