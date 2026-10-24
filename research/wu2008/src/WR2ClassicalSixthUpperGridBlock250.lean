import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints250
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_250 (j : Fin 16) : upperPayment (16*250+j.val) ≤
    upperValue ((point split endpoint 4096 (16*250+j.val)+point split endpoint 4096 (16*250+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 4000 ≤ upperValue ((point split endpoint 4096 4000+point split endpoint 4096 4001)/2)
    have hp : upperPayment 4000 = (15929918017:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4000+point split endpoint 4096 4001)/2 = (676764127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676764127:ℝ)/168755200)*ClassicalSixthBranch.v ((676764127:ℝ)/168755200)/ClassicalSixthBranch.r = (75082184708817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4000
  · change upperPayment 4001 ≤ upperValue ((point split endpoint 4096 4001+point split endpoint 4096 4002)/2)
    have hp : upperPayment 4001 = (15765123406:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4001+point split endpoint 4096 4002)/2 = (676789277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676789277:ℝ)/168755200)*ClassicalSixthBranch.v ((676789277:ℝ)/168755200)/ClassicalSixthBranch.r = (75064265704025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4001
  · change upperPayment 4002 ≤ upperValue ((point split endpoint 4096 4002+point split endpoint 4096 4003)/2)
    have hp : upperPayment 4002 = (15600286608:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4002+point split endpoint 4096 4003)/2 = (676814427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676814427:ℝ)/168755200)*ClassicalSixthBranch.v ((676814427:ℝ)/168755200)/ClassicalSixthBranch.r = (75046348723305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4002
  · change upperPayment 4003 ≤ upperValue ((point split endpoint 4096 4003+point split endpoint 4096 4004)/2)
    have hp : upperPayment 4003 = (15435407611:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4003+point split endpoint 4096 4004)/2 = (676839577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676839577:ℝ)/168755200)*ClassicalSixthBranch.v ((676839577:ℝ)/168755200)/ClassicalSixthBranch.r = (75028433766657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4003
  · change upperPayment 4004 ≤ upperValue ((point split endpoint 4096 4004+point split endpoint 4096 4005)/2)
    have hp : upperPayment 4004 = (15270486404:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4004+point split endpoint 4096 4005)/2 = (676864727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676864727:ℝ)/168755200)*ClassicalSixthBranch.v ((676864727:ℝ)/168755200)/ClassicalSixthBranch.r = (75010520834081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4004
  · change upperPayment 4005 ≤ upperValue ((point split endpoint 4096 4005+point split endpoint 4096 4006)/2)
    have hp : upperPayment 4005 = (15105522975:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4005+point split endpoint 4096 4006)/2 = (676889877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676889877:ℝ)/168755200)*ClassicalSixthBranch.v ((676889877:ℝ)/168755200)/ClassicalSixthBranch.r = (74992609925577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4005
  · change upperPayment 4006 ≤ upperValue ((point split endpoint 4096 4006+point split endpoint 4096 4007)/2)
    have hp : upperPayment 4006 = (14940517313:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4006+point split endpoint 4096 4007)/2 = (676915027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676915027:ℝ)/168755200)*ClassicalSixthBranch.v ((676915027:ℝ)/168755200)/ClassicalSixthBranch.r = (74974701041145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4006
  · change upperPayment 4007 ≤ upperValue ((point split endpoint 4096 4007+point split endpoint 4096 4008)/2)
    have hp : upperPayment 4007 = (14775469404:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4007+point split endpoint 4096 4008)/2 = (676940177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676940177:ℝ)/168755200)*ClassicalSixthBranch.v ((676940177:ℝ)/168755200)/ClassicalSixthBranch.r = (74956794180785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4007
  · change upperPayment 4008 ≤ upperValue ((point split endpoint 4096 4008+point split endpoint 4096 4009)/2)
    have hp : upperPayment 4008 = (14610379239:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4008+point split endpoint 4096 4009)/2 = (676965327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676965327:ℝ)/168755200)*ClassicalSixthBranch.v ((676965327:ℝ)/168755200)/ClassicalSixthBranch.r = (74938889344497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4008
  · change upperPayment 4009 ≤ upperValue ((point split endpoint 4096 4009+point split endpoint 4096 4010)/2)
    have hp : upperPayment 4009 = (14445246804:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4009+point split endpoint 4096 4010)/2 = (676990477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676990477:ℝ)/168755200)*ClassicalSixthBranch.v ((676990477:ℝ)/168755200)/ClassicalSixthBranch.r = (74920986532281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4009
  · change upperPayment 4010 ≤ upperValue ((point split endpoint 4096 4010+point split endpoint 4096 4011)/2)
    have hp : upperPayment 4010 = (14280072088:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4010+point split endpoint 4096 4011)/2 = (677015627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677015627:ℝ)/168755200)*ClassicalSixthBranch.v ((677015627:ℝ)/168755200)/ClassicalSixthBranch.r = (74903085744137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4010
  · change upperPayment 4011 ≤ upperValue ((point split endpoint 4096 4011+point split endpoint 4096 4012)/2)
    have hp : upperPayment 4011 = (14114855079:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4011+point split endpoint 4096 4012)/2 = (677040777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677040777:ℝ)/168755200)*ClassicalSixthBranch.v ((677040777:ℝ)/168755200)/ClassicalSixthBranch.r = (74885186980065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4011
  · change upperPayment 4012 ≤ upperValue ((point split endpoint 4096 4012+point split endpoint 4096 4013)/2)
    have hp : upperPayment 4012 = (13949595766:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4012+point split endpoint 4096 4013)/2 = (677065927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677065927:ℝ)/168755200)*ClassicalSixthBranch.v ((677065927:ℝ)/168755200)/ClassicalSixthBranch.r = (74867290240065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4012
  · change upperPayment 4013 ≤ upperValue ((point split endpoint 4096 4013+point split endpoint 4096 4014)/2)
    have hp : upperPayment 4013 = (13784294136:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4013+point split endpoint 4096 4014)/2 = (677091077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677091077:ℝ)/168755200)*ClassicalSixthBranch.v ((677091077:ℝ)/168755200)/ClassicalSixthBranch.r = (74849395524137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4013
  · change upperPayment 4014 ≤ upperValue ((point split endpoint 4096 4014+point split endpoint 4096 4015)/2)
    have hp : upperPayment 4014 = (13618950178:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4014+point split endpoint 4096 4015)/2 = (677116227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677116227:ℝ)/168755200)*ClassicalSixthBranch.v ((677116227:ℝ)/168755200)/ClassicalSixthBranch.r = (74831502832281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4014
  · change upperPayment 4015 ≤ upperValue ((point split endpoint 4096 4015+point split endpoint 4096 4016)/2)
    have hp : upperPayment 4015 = (13453563880:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4015+point split endpoint 4096 4016)/2 = (677141377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677141377:ℝ)/168755200)*ClassicalSixthBranch.v ((677141377:ℝ)/168755200)/ClassicalSixthBranch.r = (74813612164497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4015
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_250
