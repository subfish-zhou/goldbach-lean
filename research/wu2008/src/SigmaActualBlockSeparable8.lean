import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU8 : ℝ[X] := 0
def bezoutV8 : ℝ[X] := C (1)

theorem block8_separable : block8.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU8, bezoutV8, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU8, bezoutV8, block8, derivative_add,
    derivative_mul, derivative_C, derivative_X,
    eval_add, eval_mul, eval_C, eval_X, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
