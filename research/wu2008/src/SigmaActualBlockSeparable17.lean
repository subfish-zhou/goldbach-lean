import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU17 : ℝ[X] := C (85123/93210)+C (57059/186420)*X^1+C (619/31070)*X^2
def bezoutV17 : ℝ[X] := C (-29663/62140)+C (-23929/46605)*X^1+C (-38743/372840)*X^2+C (-619/124280)*X^3

theorem block17_separable : block17.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU17, bezoutV17, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU17, bezoutV17, block17, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
