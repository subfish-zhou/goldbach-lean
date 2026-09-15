import SigmaActualBlockSeparable19
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator19 : ℝ[X] := C (808178796833798268714082757699029024000/9874487820774996899585520136192543023)+C (4782083710655009295875115987278812480000/29623463462324990698756560408577629069)*X^1+C (2319796687522793323380215984165329120000/29623463462324990698756560408577629069)*X^2+C (41006123264306048000/10999300061648294361)*X^3

theorem residueNumerator19_degree : residueNumerator19.degree < block19.degree := by
  have hb : block19.degree = (4 : ℕ) := by
    unfold block19
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator19
  compute_degree; all_goals norm_num

def simplePartPrimitive19 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator19 block19

theorem simplePartPrimitive19_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive19 (residueNumerator19.eval t / block19.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block19_separable
    residueNumerator19_degree t (block19_eval_ne ht)

def principalNumerator30 : ℝ[X] := C (16322449916846414276624127885781280000/785747419493514514170885663737769)+C (-2164300812111097176398637373631488000/2357242258480543542512656991213307)*X^1+C (-97502146893122402357513412455584000/2357242258480543542512656991213307)*X^2+C (-20190880800463751223837170049856000/2357242258480543542512656991213307)*X^3
def principalPrimitive30 (t : ℝ) : ℝ := principalNumerator30.eval t / (block19.eval t)^1
def principalKernel30 (t : ℝ) : ℝ :=
  (principalNumerator30.derivative.eval t * block19.eval t -
    1*principalNumerator30.eval t*block19.derivative.eval t) / (block19.eval t)^2

theorem principalPrimitive30_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive30 (principalKernel30 t) t := by
  convert rationalPrimitive_deriv principalNumerator30 block19 0 t (block19_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel30]

def principalNumerator31 : ℝ[X] := C (-885152746789073134735977472000/4993272232960612179747)+C (-291678597512173423493289856000/14979816698881836539241)*X^1+C (-30692759060606146921112320000/4993272232960612179747)*X^2+C (-2359854683354323278339968000/14979816698881836539241)*X^3
def principalPrimitive31 (t : ℝ) : ℝ := principalNumerator31.eval t / (block19.eval t)^2
def principalKernel31 (t : ℝ) : ℝ :=
  (principalNumerator31.derivative.eval t * block19.eval t -
    2*principalNumerator31.eval t*block19.derivative.eval t) / (block19.eval t)^3

theorem principalPrimitive31_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive31 (principalKernel31 t) t := by
  exact rationalPrimitive_deriv principalNumerator31 block19 1 t (block19_eval_ne ht)

def principalNumerator32 : ℝ[X] := C (17177590154996989440000/285581476649)+C (14704928305223733760000/122392061421)*X^1+C (8049158327404710400000/122392061421)*X^2+C (4381383377506255360000/856744429947)*X^3
def principalPrimitive32 (t : ℝ) : ℝ := principalNumerator32.eval t / (block19.eval t)^3
def principalKernel32 (t : ℝ) : ℝ :=
  (principalNumerator32.derivative.eval t * block19.eval t -
    3*principalNumerator32.eval t*block19.derivative.eval t) / (block19.eval t)^4

theorem principalPrimitive32_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive32 (principalKernel32 t) t := by
  exact rationalPrimitive_deriv principalNumerator32 block19 2 t (block19_eval_ne ht)

end SigmaActualBlockSeparable
