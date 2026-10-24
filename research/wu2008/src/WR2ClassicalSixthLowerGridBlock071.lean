import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints071
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_071 (j : Fin 16) : lowerPayment (16*71+j.val) ≤
    lowerValue ((point 2 split 4096 (16*71+j.val)+point 2 split 4096 (16*71+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1136 ≤ lowerValue ((point 2 split 4096 1136+point 2 split 4096 1137)/2)
    have hp : lowerPayment 1136 = (148235877144:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1136+point 2 split 4096 1137)/2 = (403725163:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403725163:ℝ)/168755200)/ClassicalSixthBranch.v ((403725163:ℝ)/168755200) = (726148186203:ℝ)/366017494936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1136
  · change lowerPayment 1137 ≤ lowerValue ((point 2 split 4096 1137+point 2 split 4096 1138)/2)
    have hp : lowerPayment 1137 = (148342918499:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1137+point 2 split 4096 1138)/2 = (16151337:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16151337:ℝ)/6750208)/ClassicalSixthBranch.v ((16151337:ℝ)/6750208) = (726070872529:ℝ)/365969487048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1137
  · change lowerPayment 1138 ≤ lowerValue ((point 2 split 4096 1138+point 2 split 4096 1139)/2)
    have hp : lowerPayment 1138 = (148449931628:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1138+point 2 split 4096 1139)/2 = (403841687:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403841687:ℝ)/168755200)/ClassicalSixthBranch.v ((403841687:ℝ)/168755200) = (145198711771:ℝ)/73184295832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1138
  · change lowerPayment 1139 ≤ lowerValue ((point 2 split 4096 1139+point 2 split 4096 1140)/2)
    have hp : lowerPayment 1139 = (148556916559:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1139+point 2 split 4096 1140)/2 = (403899949:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403899949:ℝ)/168755200)/ClassicalSixthBranch.v ((403899949:ℝ)/168755200) = (725916245181:ℝ)/365873471272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1139
  · change lowerPayment 1140 ≤ lowerValue ((point 2 split 4096 1140+point 2 split 4096 1141)/2)
    have hp : lowerPayment 1140 = (148663873316:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1140+point 2 split 4096 1141)/2 = (403958211:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403958211:ℝ)/168755200)/ClassicalSixthBranch.v ((403958211:ℝ)/168755200) = (725838931507:ℝ)/365825463384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1140
  · change lowerPayment 1141 ≤ lowerValue ((point 2 split 4096 1141+point 2 split 4096 1142)/2)
    have hp : lowerPayment 1141 = (148770801928:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1141+point 2 split 4096 1142)/2 = (404016473:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404016473:ℝ)/168755200)/ClassicalSixthBranch.v ((404016473:ℝ)/168755200) = (725761617833:ℝ)/365777455496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1141
  · change lowerPayment 1142 ≤ lowerValue ((point 2 split 4096 1142+point 2 split 4096 1143)/2)
    have hp : lowerPayment 1142 = (148877702422:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1142+point 2 split 4096 1143)/2 = (80814947:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80814947:ℝ)/33751040)/ClassicalSixthBranch.v ((80814947:ℝ)/33751040) = (725684304159:ℝ)/365729447608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1142
  · change lowerPayment 1143 ≤ lowerValue ((point 2 split 4096 1143+point 2 split 4096 1144)/2)
    have hp : lowerPayment 1143 = (148984574823:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1143+point 2 split 4096 1144)/2 = (404132997:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404132997:ℝ)/168755200)/ClassicalSixthBranch.v ((404132997:ℝ)/168755200) = (145121398097:ℝ)/73136287944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1143
  · change lowerPayment 1144 ≤ lowerValue ((point 2 split 4096 1144+point 2 split 4096 1145)/2)
    have hp : lowerPayment 1144 = (149091419159:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1144+point 2 split 4096 1145)/2 = (404191259:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404191259:ℝ)/168755200)/ClassicalSixthBranch.v ((404191259:ℝ)/168755200) = (725529676811:ℝ)/365633431832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1144
  · change lowerPayment 1145 ≤ lowerValue ((point 2 split 4096 1145+point 2 split 4096 1146)/2)
    have hp : lowerPayment 1145 = (149198235456:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1145+point 2 split 4096 1146)/2 = (404249521:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404249521:ℝ)/168755200)/ClassicalSixthBranch.v ((404249521:ℝ)/168755200) = (725452363137:ℝ)/365585423944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1145
  · change lowerPayment 1146 ≤ lowerValue ((point 2 split 4096 1146+point 2 split 4096 1147)/2)
    have hp : lowerPayment 1146 = (149305023742:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1146+point 2 split 4096 1147)/2 = (404307783:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404307783:ℝ)/168755200)/ClassicalSixthBranch.v ((404307783:ℝ)/168755200) = (725375049463:ℝ)/365537416056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1146
  · change lowerPayment 1147 ≤ lowerValue ((point 2 split 4096 1147+point 2 split 4096 1148)/2)
    have hp : lowerPayment 1147 = (149411784042:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1147+point 2 split 4096 1148)/2 = (80873209:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80873209:ℝ)/33751040)/ClassicalSixthBranch.v ((80873209:ℝ)/33751040) = (725297735789:ℝ)/365489408168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1147
  · change lowerPayment 1148 ≤ lowerValue ((point 2 split 4096 1148+point 2 split 4096 1149)/2)
    have hp : lowerPayment 1148 = (149518516383:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1148+point 2 split 4096 1149)/2 = (404424307:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404424307:ℝ)/168755200)/ClassicalSixthBranch.v ((404424307:ℝ)/168755200) = (145044084423:ℝ)/73088280056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1148
  · change lowerPayment 1149 ≤ lowerValue ((point 2 split 4096 1149+point 2 split 4096 1150)/2)
    have hp : lowerPayment 1149 = (149625220793:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1149+point 2 split 4096 1150)/2 = (404482569:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404482569:ℝ)/168755200)/ClassicalSixthBranch.v ((404482569:ℝ)/168755200) = (725143108441:ℝ)/365393392392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1149
  · change lowerPayment 1150 ≤ lowerValue ((point 2 split 4096 1150+point 2 split 4096 1151)/2)
    have hp : lowerPayment 1150 = (149731897297:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1150+point 2 split 4096 1151)/2 = (404540831:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404540831:ℝ)/168755200)/ClassicalSixthBranch.v ((404540831:ℝ)/168755200) = (725065794767:ℝ)/365345384504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1150
  · change lowerPayment 1151 ≤ lowerValue ((point 2 split 4096 1151+point 2 split 4096 1152)/2)
    have hp : lowerPayment 1151 = (149838545923:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1151+point 2 split 4096 1152)/2 = (404599093:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404599093:ℝ)/168755200)/ClassicalSixthBranch.v ((404599093:ℝ)/168755200) = (724988481093:ℝ)/365297376616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1151
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_071
