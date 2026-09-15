import SigmaHermiteComponent4
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC

def actual4Scale : ℝ := -189
def actual4Numerator (t : ℝ) : ℝ := (250*(-5*t^2+21*t+26))*lowerNum (quadN t+(quadD t)) (2*(quadD t))
def actual4Denominator (t : ℝ) : ℝ := (189*outerQ t)*lowerDen (quadN t+(quadD t)) (2*(quadD t))*t
def actual4Weight (t : ℝ) : ℝ := (250*(-5*t^2+21*t+26))/(189*outerQ t)*(lowerNum (quadN t+(quadD t)) (2*(quadD t))/lowerDen (quadN t+(quadD t)) (2*(quadD t)))/t

theorem actual4_scale_ne : actual4Scale ≠ 0 := by
  norm_num [actual4Scale]

theorem actual4_num_identity (t : ℝ) : actual4Numerator t = actual4Scale*(((8508449448747653184000/49))+((22486565477084854752000/7))*t+((1322042515933527626976000/49))*t^2+((6724647256598038197504000/49))*t^3+((23196165301590951672000000/49))*t^4+((57275890542735518046816000/49))*t^5+((103398574421576819306400000/49))*t^6+((134912630955029776354560000/49))*t^7+(2395558392050546261656000)*t^8+((42212947140550787941772000/49))*t^9+((-166147125322526752702180000/147))*t^10+((-365815610658255614696864000/147))*t^11+((-1174866791489337579466292000/441))*t^12+((-866816595736599074392354000/441))*t^13+((-202975441783681579485622000/189))*t^14+((-83396362975250409739856000/189))*t^15+((-10893855770022709842383750/81))*t^16+((-16370185519156449234950125/567))*t^17+((-2064040861486685285843875/567))*t^18+((23964831292475307203000/567))*t^19+((79961129346087542870000/567))*t^20+((149576495419372945197500/3969))*t^21+((3594372212261489583500/567))*t^22+((3145410162954058655000/3969))*t^23+((309394514040100578500/3969))*t^24+((8197521680002284250/1323))*t^25+((1600716799966749250/3969))*t^26+((85765550501419000/3969))*t^27+((3778221895432000/3969))*t^28+((2771551619500/81))*t^29+((3920505674500/3969))*t^30+((88382401000/3969))*t^31+((1479531250/3969))*t^32+((16643125/3969))*t^33+((96875/3969))*t^34) := by
  unfold actual4Numerator actual4Scale lowerNum lowerDen qHom quadN quadD TerminalE.k TerminalE.a TerminalE.b TerminalE.c TerminalE.d TerminalE.e TerminalE.f TerminalE.g TerminalE.h
  norm_num [TerminalE.k, TerminalE.a, TerminalE.b, TerminalE.c, TerminalE.d, TerminalE.e, TerminalE.f, TerminalE.g]
  ring

theorem actual4_den_identity (t : ℝ) : actual4Denominator t = actual4Scale*((block0.eval t)*(block10.eval t)*(block18.eval t)^2*(block19.eval t)^4*(block22.eval t)) := by
  unfold actual4Denominator actual4Scale lowerDen qHom quadN quadD outerQ
  simp only [block0, block10, block18, block19, block22, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

theorem actual4_weight_kernel (t : ℝ) : actual4Weight t = component4Kernel t := by
  have he : actual4Weight t = actual4Numerator t/actual4Denominator t := by
    unfold actual4Weight actual4Numerator actual4Denominator
    simp only [div_mul_div_comm, div_div]
  rw [he, actual4_num_identity, actual4_den_identity]
  exact mul_div_mul_left _ _ actual4_scale_ne

end SigmaHermiteActualFTC
