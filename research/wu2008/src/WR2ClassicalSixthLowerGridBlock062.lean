import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints062
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_062 (j : Fin 16) : lowerPayment (16*62+j.val) ≤
    lowerValue ((point 2 split 4096 (16*62+j.val)+point 2 split 4096 (16*62+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 992 ≤ lowerValue ((point 2 split 4096 992+point 2 split 4096 993)/2)
    have hp : lowerPayment 992 = (132513246273:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 992+point 2 split 4096 993)/2 = (79067087:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79067087:ℝ)/33751040)/ClassicalSixthBranch.v ((79067087:ℝ)/33751040) = (737281355259:ℝ)/372930630808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_992
  · change lowerPayment 993 ≤ lowerValue ((point 2 split 4096 993+point 2 split 4096 994)/2)
    have hp : lowerPayment 993 = (132624642258:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 993+point 2 split 4096 994)/2 = (395393697:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395393697:ℝ)/168755200)/ClassicalSixthBranch.v ((395393697:ℝ)/168755200) = (147440808317:ℝ)/74576524584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_993
  · change lowerPayment 994 ≤ lowerValue ((point 2 split 4096 994+point 2 split 4096 995)/2)
    have hp : lowerPayment 994 = (132736005945:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 994+point 2 split 4096 995)/2 = (395451959:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395451959:ℝ)/168755200)/ClassicalSixthBranch.v ((395451959:ℝ)/168755200) = (737126727911:ℝ)/372834615032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_994
  · change lowerPayment 995 ≤ lowerValue ((point 2 split 4096 995+point 2 split 4096 996)/2)
    have hp : lowerPayment 995 = (132847337366:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 995+point 2 split 4096 996)/2 = (395510221:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395510221:ℝ)/168755200)/ClassicalSixthBranch.v ((395510221:ℝ)/168755200) = (737049414237:ℝ)/372786607144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_995
  · change lowerPayment 996 ≤ lowerValue ((point 2 split 4096 996+point 2 split 4096 997)/2)
    have hp : lowerPayment 996 = (132958636549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 996+point 2 split 4096 997)/2 = (395568483:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395568483:ℝ)/168755200)/ClassicalSixthBranch.v ((395568483:ℝ)/168755200) = (736972100563:ℝ)/372738599256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_996
  · change lowerPayment 997 ≤ lowerValue ((point 2 split 4096 997+point 2 split 4096 998)/2)
    have hp : lowerPayment 997 = (133069903524:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 997+point 2 split 4096 998)/2 = (79125349:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79125349:ℝ)/33751040)/ClassicalSixthBranch.v ((79125349:ℝ)/33751040) = (736894786889:ℝ)/372690591368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_997
  · change lowerPayment 998 ≤ lowerValue ((point 2 split 4096 998+point 2 split 4096 999)/2)
    have hp : lowerPayment 998 = (133181138320:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 998+point 2 split 4096 999)/2 = (395685007:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395685007:ℝ)/168755200)/ClassicalSixthBranch.v ((395685007:ℝ)/168755200) = (147363494643:ℝ)/74528516696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_998
  · change lowerPayment 999 ≤ lowerValue ((point 2 split 4096 999+point 2 split 4096 1000)/2)
    have hp : lowerPayment 999 = (133292340969:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 999+point 2 split 4096 1000)/2 = (395743269:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395743269:ℝ)/168755200)/ClassicalSixthBranch.v ((395743269:ℝ)/168755200) = (736740159541:ℝ)/372594575592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_999
  · change lowerPayment 1000 ≤ lowerValue ((point 2 split 4096 1000+point 2 split 4096 1001)/2)
    have hp : lowerPayment 1000 = (133403511498:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1000+point 2 split 4096 1001)/2 = (395801531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395801531:ℝ)/168755200)/ClassicalSixthBranch.v ((395801531:ℝ)/168755200) = (736662845867:ℝ)/372546567704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1000
  · change lowerPayment 1001 ≤ lowerValue ((point 2 split 4096 1001+point 2 split 4096 1002)/2)
    have hp : lowerPayment 1001 = (133514649938:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1001+point 2 split 4096 1002)/2 = (395859793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395859793:ℝ)/168755200)/ClassicalSixthBranch.v ((395859793:ℝ)/168755200) = (736585532193:ℝ)/372498559816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1001
  · change lowerPayment 1002 ≤ lowerValue ((point 2 split 4096 1002+point 2 split 4096 1003)/2)
    have hp : lowerPayment 1002 = (133625756319:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1002+point 2 split 4096 1003)/2 = (79183611:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79183611:ℝ)/33751040)/ClassicalSixthBranch.v ((79183611:ℝ)/33751040) = (736508218519:ℝ)/372450551928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1002
  · change lowerPayment 1003 ≤ lowerValue ((point 2 split 4096 1003+point 2 split 4096 1004)/2)
    have hp : lowerPayment 1003 = (133736830670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1003+point 2 split 4096 1004)/2 = (395976317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395976317:ℝ)/168755200)/ClassicalSixthBranch.v ((395976317:ℝ)/168755200) = (147286180969:ℝ)/74480508808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1003
  · change lowerPayment 1004 ≤ lowerValue ((point 2 split 4096 1004+point 2 split 4096 1005)/2)
    have hp : lowerPayment 1004 = (133847873020:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1004+point 2 split 4096 1005)/2 = (396034579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396034579:ℝ)/168755200)/ClassicalSixthBranch.v ((396034579:ℝ)/168755200) = (736353591171:ℝ)/372354536152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1004
  · change lowerPayment 1005 ≤ lowerValue ((point 2 split 4096 1005+point 2 split 4096 1006)/2)
    have hp : lowerPayment 1005 = (133958883400:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1005+point 2 split 4096 1006)/2 = (396092841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396092841:ℝ)/168755200)/ClassicalSixthBranch.v ((396092841:ℝ)/168755200) = (736276277497:ℝ)/372306528264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1005
  · change lowerPayment 1006 ≤ lowerValue ((point 2 split 4096 1006+point 2 split 4096 1007)/2)
    have hp : lowerPayment 1006 = (134069861838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1006+point 2 split 4096 1007)/2 = (396151103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396151103:ℝ)/168755200)/ClassicalSixthBranch.v ((396151103:ℝ)/168755200) = (736198963823:ℝ)/372258520376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1006
  · change lowerPayment 1007 ≤ lowerValue ((point 2 split 4096 1007+point 2 split 4096 1008)/2)
    have hp : lowerPayment 1007 = (134180808364:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1007+point 2 split 4096 1008)/2 = (79241873:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79241873:ℝ)/33751040)/ClassicalSixthBranch.v ((79241873:ℝ)/33751040) = (736121650149:ℝ)/372210512488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1007
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_062
