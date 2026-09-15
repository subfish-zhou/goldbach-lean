import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU18 : ℝ[X] := C (560653/1271310)+C (675539/7627860)*X^1+C (21913/3813930)*X^2
def bezoutV18 : ℝ[X] := C (-573109/2542620)+C (-149998/635655)*X^1+C (-458291/15255720)*X^2+C (-21913/15255720)*X^3

theorem block18_separable : block18.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU18, bezoutV18, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU18, bezoutV18, block18, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
