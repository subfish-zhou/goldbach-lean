import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU14 : ℝ[X] := C ((-4309/3600)+(53/180)*TerminalE.radical)
def bezoutV14 : ℝ[X] := C ((3097/2400)+(-5/18)*TerminalE.radical)+C ((4309/7200)+(-53/360)*TerminalE.radical)*X^1

theorem block14_separable : block14.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU14, bezoutV14, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU14, bezoutV14, block14, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring_nf
  rw [TerminalE.radical_sq]
  ring

end SigmaActualBlockSeparable
