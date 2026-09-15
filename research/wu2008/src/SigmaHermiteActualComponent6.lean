import SigmaHermiteComponent6
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC

def actual6Scale : ℝ := -189*TerminalE.radical*lowerDen 10 (10-2*TerminalE.radical)
def actual6Numerator (t : ℝ) : ℝ := (250*(-11*t^2+97*t+108))*lowerNum (radN t+(radD t)) (2*(radD t))
def actual6Denominator (t : ℝ) : ℝ := (189*TerminalE.radical*outerQ t)*lowerDen (radN t+(radD t)) (2*(radD t))*t
def actual6Weight (t : ℝ) : ℝ := (250*(-11*t^2+97*t+108))/(189*TerminalE.radical*outerQ t)*(lowerNum (radN t+(radD t)) (2*(radD t))/lowerDen (radN t+(radD t)) (2*(radD t)))/t

theorem actual6_scale_ne : actual6Scale ≠ 0 := by
  have hr := TerminalE.radical_pos
  have hm : 0 < 10-2*TerminalE.radical := by linarith [TerminalE.radical_lt_four]
  have hp : 0 < 10+2*TerminalE.radical := by positivity
  have hd := lowerDen_pos (by norm_num : (0:ℝ)<10) hm
  unfold actual6Scale
  exact mul_ne_zero (mul_ne_zero (by norm_num) hr.ne') hd.ne'

theorem actual6_num_identity (t : ℝ) : actual6Numerator t = actual6Scale*((((448354787778360/315124733)+(115392069589572/315124733)*TerminalE.radical))+(((94815533250150/45017819)+(72926716295023/135053457)*TerminalE.radical))*t+(((-48138041624830/315124733)+(-41084992382411/945374199)*TerminalE.radical))*t^2+(((-49069894840040/28647703)+(-114021512659564/257829327)*TerminalE.radical))*t^3+(((-51303275480/42483)+(-39278583100/127449)*TerminalE.radical))*t^4+(((-158018744438540/405160371)+(-39402410283146/405160371)*TerminalE.radical))*t^5+(((-76378329366100/1215481113)+(-5943087951554/405160371)*TerminalE.radical))*t^6+(((-28638383085640/8508367791)+(-4364633774236/8508367791)*TerminalE.radical))*t^7+(((518476759840/1215481113)+(168437325136/1215481113)*TerminalE.radical))*t^8+(((654999508510/8508367791)+(142040899465/8508367791)*TerminalE.radical))*t^9+(((997739590/257829327)+(342491167/773487981)*TerminalE.radical))*t^10) := by
  unfold actual6Numerator actual6Scale lowerNum lowerDen qHom radN radD TerminalE.k TerminalE.a TerminalE.b TerminalE.c TerminalE.d TerminalE.e TerminalE.f TerminalE.g TerminalE.h
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

theorem actual6_den_identity (t : ℝ) : actual6Denominator t = actual6Scale*((block0.eval t)*(block3.eval t)^2*(block5.eval t)^4*(block10.eval t)*(block14.eval t)) := by
  unfold actual6Denominator actual6Scale lowerDen qHom radN radD outerQ
  simp only [block0, block3, block5, block10, block14, eval_add, eval_mul, eval_pow, eval_X, eval_C]
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

theorem actual6_weight_kernel (t : ℝ) : actual6Weight t = component6Kernel t := by
  have he : actual6Weight t = actual6Numerator t/actual6Denominator t := by
    unfold actual6Weight actual6Numerator actual6Denominator
    simp only [div_mul_div_comm, div_div]
  rw [he, actual6_num_identity, actual6_den_identity]
  exact mul_div_mul_left _ _ actual6_scale_ne

end SigmaHermiteActualFTC
