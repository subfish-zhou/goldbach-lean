import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU20 : ℝ[X] := C (-87375619/593698140)+C (-11525671/558774720)*X^1+C (-224209/949917024)*X^2
def bezoutV20 : ℝ[X] := C (6106985/79159752)+C (367502911/4749585120)*X^1+C (43679677/6332780160)*X^2+C (224209/3799668096)*X^3

theorem block20_separable : block20.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU20, bezoutV20, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU20, bezoutV20, block20, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
