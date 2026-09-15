import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU3 : ℝ[X] := 0
def bezoutV3 : ℝ[X] := C (1)

theorem block3_separable : block3.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU3, bezoutV3, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU3, bezoutV3, block3, derivative_add,
    derivative_mul, derivative_C, derivative_X,
    eval_add, eval_mul, eval_C, eval_X, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
