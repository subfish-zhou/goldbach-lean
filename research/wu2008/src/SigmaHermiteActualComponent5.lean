import SigmaHermiteComponent5
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC

def actual5Scale : ℝ := -1285956
def actual5Numerator (t : ℝ) : ℝ := (250*(-5*t^2+21*t+26))*lowerNum (2*(quadN t)) (quadN t+(quadD t))
def actual5Denominator (t : ℝ) : ℝ := (189*outerQ t)*lowerDen (2*(quadN t)) (quadN t+(quadD t))*t
def actual5Weight (t : ℝ) : ℝ := (250*(-5*t^2+21*t+26))/(189*outerQ t)*(lowerNum (2*(quadN t)) (quadN t+(quadD t))/lowerDen (2*(quadN t)) (quadN t+(quadD t)))/t

theorem actual5_scale_ne : actual5Scale ≠ 0 := by
  norm_num [actual5Scale]

theorem actual5_num_identity (t : ℝ) : actual5Numerator t = actual5Scale*(((60068004392489600/3))+((370763365890454686400/1029))*t+((9128521850534939377600/3087))*t^2+((45746007963891593292800/3087))*t^3+((471891456387823917776000/9261))*t^4+((1180326920044020780923200/9261))*t^5+((6625956870173629851092800/27783))*t^6+((1328790738032779442595200/3969))*t^7+((28323416416052604945203600/83349))*t^8+((17532321935943721735429000/83349))*t^9+((-3102573073073326212771800/250047))*t^10+((-55665964746475579780482400/250047))*t^11+((-246446986470997465362244600/750141))*t^12+((-234830846543478112332014300/750141))*t^13+((-72454096429549311509634500/321489))*t^14+((-41345250196192362464337400/321489))*t^15+((-16304510741880503942169725/275562))*t^16+((-84818810069093258175959075/3857868))*t^17+((-25160377995711896052891725/3857868))*t^18+((-1440617078155157137412750/964467))*t^19+((-231832161686194801327100/964467))*t^20+((-2350076109818363545775/137781))*t^21+((27226413874421623414075/6751269))*t^22+((12341711994494378967850/6751269))*t^23+((2723499357708127351375/6751269))*t^24+((280733559541175512675/4500846))*t^25+((98481671235840878575/13502538))*t^26+((4456338770626722050/6751269))*t^27+((912998254038800/19683))*t^28+((16941849507717125/6751269))*t^29+((691932191185775/6751269))*t^30+((20617356015950/6751269))*t^31+((844972133575/13502538))*t^32+((21268346075/27005076))*t^33+((123797125/27005076))*t^34) := by
  unfold actual5Numerator actual5Scale lowerNum lowerDen qHom quadN quadD TerminalE.k TerminalE.a TerminalE.b TerminalE.c TerminalE.d TerminalE.e TerminalE.f TerminalE.g TerminalE.h
  norm_num [TerminalE.k, TerminalE.a, TerminalE.b, TerminalE.c, TerminalE.d, TerminalE.e, TerminalE.f, TerminalE.g]
  ring

theorem actual5_den_identity (t : ℝ) : actual5Denominator t = actual5Scale*((block0.eval t)*(block2.eval t)^4*(block7.eval t)^2*(block8.eval t)^2*(block10.eval t)*(block17.eval t)^4*(block21.eval t)) := by
  unfold actual5Denominator actual5Scale lowerDen qHom quadN quadD outerQ
  simp only [block0, block2, block7, block8, block10, block17, block21, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  have hr3 : TerminalE.radical^3 = 15*TerminalE.radical^1 := radical_power_reduce 1
  have hr4 : TerminalE.radical^4 = 15*TerminalE.radical^2 := radical_power_reduce 2
  ring_nf
  repeat first
    | rw [hr4]
    | rw [hr3]
    | rw [TerminalE.radical_sq]
  ring

theorem actual5_weight_kernel (t : ℝ) : actual5Weight t = component5Kernel t := by
  have he : actual5Weight t = actual5Numerator t/actual5Denominator t := by
    unfold actual5Weight actual5Numerator actual5Denominator
    simp only [div_mul_div_comm, div_div]
  rw [he, actual5_num_identity, actual5_den_identity]
  exact mul_div_mul_left _ _ actual5_scale_ne

end SigmaHermiteActualFTC
