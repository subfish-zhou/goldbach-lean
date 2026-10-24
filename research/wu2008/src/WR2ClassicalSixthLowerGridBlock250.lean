import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints250
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_250 (j : Fin 16) : lowerPayment (16*250+j.val) ≤
    lowerValue ((point 2 split 4096 (16*250+j.val)+point 2 split 4096 (16*250+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 4000 ≤ lowerValue ((point 2 split 4096 4000+point 2 split 4096 4001)/2)
    have hp : lowerPayment 4000 = (414591101317:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4000+point 2 split 4096 4001)/2 = (570587531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570587531:ℝ)/168755200)/ClassicalSixthBranch.v ((570587531:ℝ)/168755200) = (504721823867:ℝ)/228522903704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4000
  · change lowerPayment 4001 ≤ lowerValue ((point 2 split 4096 4001+point 2 split 4096 4002)/2)
    have hp : lowerPayment 4001 = (414691825166:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4001+point 2 split 4096 4002)/2 = (570645793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570645793:ℝ)/168755200)/ClassicalSixthBranch.v ((570645793:ℝ)/168755200) = (504644510193:ℝ)/228474895816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4001
  · change lowerPayment 4002 ≤ lowerValue ((point 2 split 4096 4002+point 2 split 4096 4003)/2)
    have hp : lowerPayment 4002 = (414792569542:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4002+point 2 split 4096 4003)/2 = (114140811:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114140811:ℝ)/33751040)/ClassicalSixthBranch.v ((114140811:ℝ)/33751040) = (504567196519:ℝ)/228426887928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4002
  · change lowerPayment 4003 ≤ lowerValue ((point 2 split 4096 4003+point 2 split 4096 4004)/2)
    have hp : lowerPayment 4003 = (414893334463:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4003+point 2 split 4096 4004)/2 = (570762317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570762317:ℝ)/168755200)/ClassicalSixthBranch.v ((570762317:ℝ)/168755200) = (100897976569:ℝ)/45675776008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4003
  · change lowerPayment 4004 ≤ lowerValue ((point 2 split 4096 4004+point 2 split 4096 4005)/2)
    have hp : lowerPayment 4004 = (414994119949:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4004+point 2 split 4096 4005)/2 = (570820579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570820579:ℝ)/168755200)/ClassicalSixthBranch.v ((570820579:ℝ)/168755200) = (504412569171:ℝ)/228330872152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4004
  · change lowerPayment 4005 ≤ lowerValue ((point 2 split 4096 4005+point 2 split 4096 4006)/2)
    have hp : lowerPayment 4005 = (415094926017:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4005+point 2 split 4096 4006)/2 = (570878841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570878841:ℝ)/168755200)/ClassicalSixthBranch.v ((570878841:ℝ)/168755200) = (504335255497:ℝ)/228282864264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4005
  · change lowerPayment 4006 ≤ lowerValue ((point 2 split 4096 4006+point 2 split 4096 4007)/2)
    have hp : lowerPayment 4006 = (415195752688:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4006+point 2 split 4096 4007)/2 = (570937103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570937103:ℝ)/168755200)/ClassicalSixthBranch.v ((570937103:ℝ)/168755200) = (504257941823:ℝ)/228234856376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4006
  · change lowerPayment 4007 ≤ lowerValue ((point 2 split 4096 4007+point 2 split 4096 4008)/2)
    have hp : lowerPayment 4007 = (415296599980:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4007+point 2 split 4096 4008)/2 = (114199073:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114199073:ℝ)/33751040)/ClassicalSixthBranch.v ((114199073:ℝ)/33751040) = (504180628149:ℝ)/228186848488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4007
  · change lowerPayment 4008 ≤ lowerValue ((point 2 split 4096 4008+point 2 split 4096 4009)/2)
    have hp : lowerPayment 4008 = (415397467911:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4008+point 2 split 4096 4009)/2 = (571053627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571053627:ℝ)/168755200)/ClassicalSixthBranch.v ((571053627:ℝ)/168755200) = (20164132579:ℝ)/9125553624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4008
  · change lowerPayment 4009 ≤ lowerValue ((point 2 split 4096 4009+point 2 split 4096 4010)/2)
    have hp : lowerPayment 4009 = (415498356502:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4009+point 2 split 4096 4010)/2 = (571111889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571111889:ℝ)/168755200)/ClassicalSixthBranch.v ((571111889:ℝ)/168755200) = (504026000801:ℝ)/228090832712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4009
  · change lowerPayment 4010 ≤ lowerValue ((point 2 split 4096 4010+point 2 split 4096 4011)/2)
    have hp : lowerPayment 4010 = (415599265771:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4010+point 2 split 4096 4011)/2 = (571170151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571170151:ℝ)/168755200)/ClassicalSixthBranch.v ((571170151:ℝ)/168755200) = (503948687127:ℝ)/228042824824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4010
  · change lowerPayment 4011 ≤ lowerValue ((point 2 split 4096 4011+point 2 split 4096 4012)/2)
    have hp : lowerPayment 4011 = (415700195736:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4011+point 2 split 4096 4012)/2 = (571228413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571228413:ℝ)/168755200)/ClassicalSixthBranch.v ((571228413:ℝ)/168755200) = (503871373453:ℝ)/227994816936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4011
  · change lowerPayment 4012 ≤ lowerValue ((point 2 split 4096 4012+point 2 split 4096 4013)/2)
    have hp : lowerPayment 4012 = (415801146418:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4012+point 2 split 4096 4013)/2 = (22851467:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22851467:ℝ)/6750208)/ClassicalSixthBranch.v ((22851467:ℝ)/6750208) = (503794059779:ℝ)/227946809048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4012
  · change lowerPayment 4013 ≤ lowerValue ((point 2 split 4096 4013+point 2 split 4096 4014)/2)
    have hp : lowerPayment 4013 = (415902117835:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4013+point 2 split 4096 4014)/2 = (571344937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571344937:ℝ)/168755200)/ClassicalSixthBranch.v ((571344937:ℝ)/168755200) = (100743349221:ℝ)/45579760232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4013
  · change lowerPayment 4014 ≤ lowerValue ((point 2 split 4096 4014+point 2 split 4096 4015)/2)
    have hp : lowerPayment 4014 = (416003110005:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4014+point 2 split 4096 4015)/2 = (571403199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571403199:ℝ)/168755200)/ClassicalSixthBranch.v ((571403199:ℝ)/168755200) = (503639432431:ℝ)/227850793272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4014
  · change lowerPayment 4015 ≤ lowerValue ((point 2 split 4096 4015+point 2 split 4096 4016)/2)
    have hp : lowerPayment 4015 = (416104122949:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4015+point 2 split 4096 4016)/2 = (571461461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571461461:ℝ)/168755200)/ClassicalSixthBranch.v ((571461461:ℝ)/168755200) = (503562118757:ℝ)/227802785384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4015
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_250
