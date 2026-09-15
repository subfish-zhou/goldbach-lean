import SigmaHermiteComponent2
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC

def actual2Scale : ℝ := 945
def actual2Numerator (t : ℝ) : ℝ := (64*(10*t^4+18*t^3-t^2-6*t+3))*lowerNum (negN t+(negD t)) (2*(negD t))
def actual2Denominator (t : ℝ) : ℝ := (945*t^4)*lowerDen (negN t+(negD t)) (2*(negD t))*t
def actual2Weight (t : ℝ) : ℝ := (64*(10*t^4+18*t^3-t^2-6*t+3))/(945*t^4)*(lowerNum (negN t+(negD t)) (2*(negD t))/lowerDen (negN t+(negD t)) (2*(negD t)))/t

theorem actual2_scale_ne : actual2Scale ≠ 0 := by
  norm_num [actual2Scale]

theorem actual2_num_identity (t : ℝ) : actual2Numerator t = actual2Scale*(((-8153726976/7))*t+((-29557260288/7))*t^2+((-39758856192/35))*t^3+((341638250496/35))*t^4+((-369194819584/35))*t^5+((-9362386895872/105))*t^6+((-1614741497924096/11025))*t^7+((-2761988230732576/33075))*t^8+((548938408808896/11025))*t^9+((11973108494440096/99225))*t^10+((9598264293025984/99225))*t^11+((487361650776064/11025))*t^12+((414453113564288/33075))*t^13+((74204065476032/33075))*t^14+((2831080249216/11025))*t^15+((624006729952/33075))*t^16+((29052831296/33075))*t^17+((30431264/1225))*t^18+((7658176/19845))*t^19+((9920/3969))*t^20) := by
  unfold actual2Numerator actual2Scale lowerNum lowerDen qHom negN negD TerminalE.k TerminalE.a TerminalE.b TerminalE.c TerminalE.d TerminalE.e TerminalE.f TerminalE.g TerminalE.h
  norm_num [TerminalE.k, TerminalE.a, TerminalE.b, TerminalE.c, TerminalE.d, TerminalE.e, TerminalE.f, TerminalE.g]
  ring

theorem actual2_den_identity (t : ℝ) : actual2Denominator t = actual2Scale*((block0.eval t)^5*(block12.eval t)^2*(block15.eval t)^4*(block20.eval t)) := by
  unfold actual2Denominator actual2Scale lowerDen qHom negN negD
  simp only [block0, block12, block15, block20, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

theorem actual2_weight_kernel (t : ℝ) : actual2Weight t = component2Kernel t := by
  have he : actual2Weight t = actual2Numerator t/actual2Denominator t := by
    unfold actual2Weight actual2Numerator actual2Denominator
    simp only [div_mul_div_comm, div_div]
  rw [he, actual2_num_identity, actual2_den_identity]
  exact mul_div_mul_left _ _ actual2_scale_ne

end SigmaHermiteActualFTC
