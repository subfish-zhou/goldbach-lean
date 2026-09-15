import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU16 : ℝ[X] := C (-452249/144840)+C (-1880441/1158720)*X^1+C (-19495/115872)*X^2
def bezoutV16 : ℝ[X] := C (17309/9656)+C (1142053/579360)*X^1+C (436411/772480)*X^2+C (19495/463488)*X^3

theorem block16_separable : block16.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU16, bezoutV16, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU16, bezoutV16, block16, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
