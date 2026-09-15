import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU4 : ℝ[X] := 0
def bezoutV4 : ℝ[X] := C (1)

theorem block4_separable : block4.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU4, bezoutV4, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU4, bezoutV4, block4, derivative_add,
    derivative_mul, derivative_C, derivative_X,
    eval_add, eval_mul, eval_C, eval_X, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
