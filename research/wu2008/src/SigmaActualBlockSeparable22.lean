import SigmaSimpleResidueDerivative
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Literal witness from the saved fixed Bezout certificate; no recomputation. -/
def bezoutU22 : ℝ[X] := C (306407173642331466143/49061365576419420000)+C (5817571792111279331833/470989109533626432000)*X^1+C (5022693011742452597153/706483664300439648000)*X^2+C (4649302055997768615409/4709891095336264320000)*X^3+C (230202779887618197991/3532418321502198240000)*X^4+C (6828852625541865599/4709891095336264320000)*X^5+C (272741908599594359/7064836643004396480000)*X^6
def bezoutV22 : ℝ[X] := C (-356280563282936740721/224280528349345920000)+C (-864516304806435123403/188395643813450572800)*X^1+C (-3638399573926520557537/784981849222710720000)*X^2+C (-6436264709060209779193/3532418321502198240000)*X^3+C (-1610353744739892155689/8074099020576453120000)*X^4+C (-205226907093486546967/18839564381345057280000)*X^5+C (-16287599771998013/78389310879383040000)*X^6+C (-272741908599594359/56518693144035171840000)*X^7

theorem block22_separable : block22.Separable := by
  apply (Polynomial.separable_def' _).2
  refine ⟨bezoutU22, bezoutV22, ?_⟩
  apply Polynomial.funext
  intro t
  simp only [bezoutU22, bezoutV22, block22, derivative_add,
    derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero,
    eval_one]
  ring

end SigmaActualBlockSeparable
