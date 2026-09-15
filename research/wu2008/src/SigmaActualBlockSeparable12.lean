import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU12 : ℝ[X] := C (-4/73)
def bezoutV12 : ℝ[X] := C (11/73)+C (2/73)*X^1

theorem block12_separable : block12.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU12, bezoutV12, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU12, bezoutV12, block12, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
