import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU0 : ℝ[X] := 0
def bezoutV0 : ℝ[X] := C (1)

theorem block0_separable : block0.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU0, bezoutV0, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU0, bezoutV0, block0,
    derivative_mul, derivative_C, derivative_X,
    eval_add, eval_mul, eval_C, eval_X, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
