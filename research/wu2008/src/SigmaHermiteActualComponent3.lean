import SigmaHermiteComponent3
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC

def actual3Scale : ℝ := 6429780
def actual3Numerator (t : ℝ) : ℝ := (64*(10*t^4+18*t^3-t^2-6*t+3))*lowerNum (2*(negN t)) (negN t+(negD t))
def actual3Denominator (t : ℝ) : ℝ := (945*t^4)*lowerDen (2*(negN t)) (negN t+(negD t))*t
def actual3Weight (t : ℝ) : ℝ := (64*(10*t^4+18*t^3-t^2-6*t+3))/(945*t^4)*(lowerNum (2*(negN t)) (negN t+(negD t))/lowerDen (2*(negN t)) (negN t+(negD t)))/t

theorem actual3_scale_ne : actual3Scale ≠ 0 := by
  norm_num [actual3Scale]

theorem actual3_num_identity (t : ℝ) : actual3Numerator t = actual3Scale*(((-8388608/49))*t+((-76546048/147))*t^2+((-160694272/6615))*t^3+((20166443008/19845))*t^4+((-116207908864/59535))*t^5+((-4829944576/441))*t^6+((-12132910026112/694575))*t^7+((-13592064082232/1148175))*t^8+((127043907066032/56260575))*t^9+((423468259626232/33756345))*t^10+((2246635195046096/168781725))*t^11+((478157819250176/56260575))*t^12+((70504072775072/18753525))*t^13+((22556737823024/18753525))*t^14+((90424525472/321489))*t^15+((2681467699528/56260575))*t^16+((106814201552/18753525))*t^17+((2842229608/6251175))*t^18+((3667389328/168781725))*t^19+((15846032/33756345))*t^20) := by
  unfold actual3Numerator actual3Scale lowerNum lowerDen qHom negN negD TerminalE.k TerminalE.a TerminalE.b TerminalE.c TerminalE.d TerminalE.e TerminalE.f TerminalE.g TerminalE.h
  norm_num [TerminalE.k, TerminalE.a, TerminalE.b, TerminalE.c, TerminalE.d, TerminalE.e, TerminalE.f, TerminalE.g]
  ring

theorem actual3_den_identity (t : ℝ) : actual3Denominator t = actual3Scale*((block0.eval t)^5*(block2.eval t)^2*(block3.eval t)^2*(block11.eval t)^4*(block16.eval t)) := by
  unfold actual3Denominator actual3Scale lowerDen qHom negN negD
  simp only [block0, block2, block3, block11, block16, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

theorem actual3_weight_kernel (t : ℝ) : actual3Weight t = component3Kernel t := by
  have he : actual3Weight t = actual3Numerator t/actual3Denominator t := by
    unfold actual3Weight actual3Numerator actual3Denominator
    simp only [div_mul_div_comm, div_div]
  rw [he, actual3_num_identity, actual3_den_identity]
  exact mul_div_mul_left _ _ actual3_scale_ne

end SigmaHermiteActualFTC
