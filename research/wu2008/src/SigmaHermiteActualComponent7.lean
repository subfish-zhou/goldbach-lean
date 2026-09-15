import SigmaHermiteComponent7
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC

def actual7Scale : ℝ := -189*TerminalE.radical*lowerDen (10+2*TerminalE.radical) 10
def actual7Numerator (t : ℝ) : ℝ := (250*(-11*t^2+97*t+108))*lowerNum (2*(radN t)) (radN t+(radD t))
def actual7Denominator (t : ℝ) : ℝ := (189*TerminalE.radical*outerQ t)*lowerDen (2*(radN t)) (radN t+(radD t))*t
def actual7Weight (t : ℝ) : ℝ := (250*(-11*t^2+97*t+108))/(189*TerminalE.radical*outerQ t)*(lowerNum (2*(radN t)) (radN t+(radD t))/lowerDen (2*(radN t)) (radN t+(radD t)))/t

theorem actual7_scale_ne : actual7Scale ≠ 0 := by
  have hr := TerminalE.radical_pos
  have hm : 0 < 10-2*TerminalE.radical := by linarith [TerminalE.radical_lt_four]
  have hp : 0 < 10+2*TerminalE.radical := by positivity
  have hd := lowerDen_pos hp (by norm_num : (0:ℝ)<10)
  unfold actual7Scale
  exact mul_ne_zero (mul_ne_zero (by norm_num) hr.ne') hd.ne'

theorem actual7_num_identity (t : ℝ) : actual7Numerator t = actual7Scale*((((284647935100950/6431117)+(-514461163909500/45017819)*TerminalE.radical))+(((2359152189314275/57295406)+(-913621735233875/85943109)*TerminalE.radical))*t+(((-55585160603185625/1890748398)+(2392415196384625/315124733)*TerminalE.radical))*t^2+(((-36592060920933250/945374199)+(28345721359890500/2836122597)*TerminalE.radical))*t^3+(((-542582783715850/36832761)+(140067708857500/36832761)*TerminalE.radical))*t^4+(((-91497542537125/36832761)+(70741495702250/110498283)*TerminalE.radical))*t^5+(((-9597243014225/71498889)+(2423846285750/71498889)*TerminalE.radical))*t^6+(((18444005374250/1215481113)+(-561737493500/135053457)*TerminalE.radical))*t^7+(((22666304077000/8508367791)+(-6124931774000/8508367791)*TerminalE.radical))*t^8+(((2544927371075/17016735582)+(-317998500625/8508367791)*TerminalE.radical))*t^9+(((2013863975/515658654)+(-349618375/773487981)*TerminalE.radical))*t^10) := by
  unfold actual7Numerator actual7Scale lowerNum lowerDen qHom radN radD TerminalE.k TerminalE.a TerminalE.b TerminalE.c TerminalE.d TerminalE.e TerminalE.f TerminalE.g TerminalE.h
  norm_num [TerminalE.k, TerminalE.a, TerminalE.b, TerminalE.c, TerminalE.d, TerminalE.e, TerminalE.f, TerminalE.g]
  have hr3 : TerminalE.radical^3 = 15*TerminalE.radical^1 := radical_power_reduce 1
  have hr4 : TerminalE.radical^4 = 15*TerminalE.radical^2 := radical_power_reduce 2
  have hr5 : TerminalE.radical^5 = 15*TerminalE.radical^3 := radical_power_reduce 3
  have hr6 : TerminalE.radical^6 = 15*TerminalE.radical^4 := radical_power_reduce 4
  have hr7 : TerminalE.radical^7 = 15*TerminalE.radical^5 := radical_power_reduce 5
  have hr8 : TerminalE.radical^8 = 15*TerminalE.radical^6 := radical_power_reduce 6
  have hr9 : TerminalE.radical^9 = 15*TerminalE.radical^7 := radical_power_reduce 7
  have hr10 : TerminalE.radical^10 = 15*TerminalE.radical^8 := radical_power_reduce 8
  have hr11 : TerminalE.radical^11 = 15*TerminalE.radical^9 := radical_power_reduce 9
  have hr12 : TerminalE.radical^12 = 15*TerminalE.radical^10 := radical_power_reduce 10
  have hr13 : TerminalE.radical^13 = 15*TerminalE.radical^11 := radical_power_reduce 11
  have hr14 : TerminalE.radical^14 = 15*TerminalE.radical^12 := radical_power_reduce 12
  have hr15 : TerminalE.radical^15 = 15*TerminalE.radical^13 := radical_power_reduce 13
  have hr16 : TerminalE.radical^16 = 15*TerminalE.radical^14 := radical_power_reduce 14
  have hr17 : TerminalE.radical^17 = 15*TerminalE.radical^15 := radical_power_reduce 15
  ring_nf
  repeat first
    | rw [hr17]
    | rw [hr16]
    | rw [hr15]
    | rw [hr14]
    | rw [hr13]
    | rw [hr12]
    | rw [hr11]
    | rw [hr10]
    | rw [hr9]
    | rw [hr8]
    | rw [hr7]
    | rw [hr6]
    | rw [hr5]
    | rw [hr4]
    | rw [hr3]
    | rw [TerminalE.radical_sq]
  ring

theorem actual7_den_identity (t : ℝ) : actual7Denominator t = actual7Scale*((block0.eval t)*(block4.eval t)^4*(block7.eval t)^2*(block10.eval t)*(block13.eval t)) := by
  unfold actual7Denominator actual7Scale lowerDen qHom radN radD outerQ
  simp only [block0, block4, block7, block10, block13, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  have hr3 : TerminalE.radical^3 = 15*TerminalE.radical^1 := radical_power_reduce 1
  have hr4 : TerminalE.radical^4 = 15*TerminalE.radical^2 := radical_power_reduce 2
  have hr5 : TerminalE.radical^5 = 15*TerminalE.radical^3 := radical_power_reduce 3
  have hr6 : TerminalE.radical^6 = 15*TerminalE.radical^4 := radical_power_reduce 4
  have hr7 : TerminalE.radical^7 = 15*TerminalE.radical^5 := radical_power_reduce 5
  have hr8 : TerminalE.radical^8 = 15*TerminalE.radical^6 := radical_power_reduce 6
  have hr9 : TerminalE.radical^9 = 15*TerminalE.radical^7 := radical_power_reduce 7
  have hr10 : TerminalE.radical^10 = 15*TerminalE.radical^8 := radical_power_reduce 8
  have hr11 : TerminalE.radical^11 = 15*TerminalE.radical^9 := radical_power_reduce 9
  have hr12 : TerminalE.radical^12 = 15*TerminalE.radical^10 := radical_power_reduce 10
  have hr13 : TerminalE.radical^13 = 15*TerminalE.radical^11 := radical_power_reduce 11
  have hr14 : TerminalE.radical^14 = 15*TerminalE.radical^12 := radical_power_reduce 12
  have hr15 : TerminalE.radical^15 = 15*TerminalE.radical^13 := radical_power_reduce 13
  have hr16 : TerminalE.radical^16 = 15*TerminalE.radical^14 := radical_power_reduce 14
  have hr17 : TerminalE.radical^17 = 15*TerminalE.radical^15 := radical_power_reduce 15
  ring_nf
  repeat first
    | rw [hr17]
    | rw [hr16]
    | rw [hr15]
    | rw [hr14]
    | rw [hr13]
    | rw [hr12]
    | rw [hr11]
    | rw [hr10]
    | rw [hr9]
    | rw [hr8]
    | rw [hr7]
    | rw [hr6]
    | rw [hr5]
    | rw [hr4]
    | rw [hr3]
    | rw [TerminalE.radical_sq]
  ring

theorem actual7_weight_kernel (t : ℝ) : actual7Weight t = component7Kernel t := by
  have he : actual7Weight t = actual7Numerator t/actual7Denominator t := by
    unfold actual7Weight actual7Numerator actual7Denominator
    simp only [div_mul_div_comm, div_div]
  rw [he, actual7_num_identity, actual7_den_identity]
  exact mul_div_mul_left _ _ actual7_scale_ne

end SigmaHermiteActualFTC
