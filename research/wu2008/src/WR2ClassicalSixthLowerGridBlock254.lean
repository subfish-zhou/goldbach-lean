import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints254
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_254 (j : Fin 16) : lowerPayment (16*254+j.val) ≤
    lowerValue ((point 2 split 4096 (16*254+j.val)+point 2 split 4096 (16*254+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 4064 ≤ lowerValue ((point 2 split 4096 4064+point 2 split 4096 4065)/2)
    have hp : lowerPayment 4064 = (421079603096:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4064+point 2 split 4096 4065)/2 = (574316299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574316299:ℝ)/168755200)/ClassicalSixthBranch.v ((574316299:ℝ)/168755200) = (499773748731:ℝ)/225450398872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4064
  · change lowerPayment 4065 ≤ lowerValue ((point 2 split 4096 4065+point 2 split 4096 4066)/2)
    have hp : lowerPayment 4065 = (421181679169:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4065+point 2 split 4096 4066)/2 = (574374561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574374561:ℝ)/168755200)/ClassicalSixthBranch.v ((574374561:ℝ)/168755200) = (499696435057:ℝ)/225402390984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4065
  · change lowerPayment 4066 ≤ lowerValue ((point 2 split 4096 4066+point 2 split 4096 4067)/2)
    have hp : lowerPayment 4066 = (421283777000:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4066+point 2 split 4096 4067)/2 = (574432823:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574432823:ℝ)/168755200)/ClassicalSixthBranch.v ((574432823:ℝ)/168755200) = (499619121383:ℝ)/225354383096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4066
  · change lowerPayment 4067 ≤ lowerValue ((point 2 split 4096 4067+point 2 split 4096 4068)/2)
    have hp : lowerPayment 4067 = (421385896606:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4067+point 2 split 4096 4068)/2 = (114898217:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114898217:ℝ)/33751040)/ClassicalSixthBranch.v ((114898217:ℝ)/33751040) = (499541807709:ℝ)/225306375208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4067
  · change lowerPayment 4068 ≤ lowerValue ((point 2 split 4096 4068+point 2 split 4096 4069)/2)
    have hp : lowerPayment 4068 = (421488038008:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4068+point 2 split 4096 4069)/2 = (5578149:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((5578149:ℝ)/1638400)/ClassicalSixthBranch.v ((5578149:ℝ)/1638400) = (969833969:ℝ)/437394888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4068
  · change lowerPayment 4069 ≤ lowerValue ((point 2 split 4096 4069+point 2 split 4096 4070)/2)
    have hp : lowerPayment 4069 = (421590201225:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4069+point 2 split 4096 4070)/2 = (574607609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574607609:ℝ)/168755200)/ClassicalSixthBranch.v ((574607609:ℝ)/168755200) = (499387180361:ℝ)/225210359432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4069
  · change lowerPayment 4070 ≤ lowerValue ((point 2 split 4096 4070+point 2 split 4096 4071)/2)
    have hp : lowerPayment 4070 = (421692386277:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4070+point 2 split 4096 4071)/2 = (574665871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574665871:ℝ)/168755200)/ClassicalSixthBranch.v ((574665871:ℝ)/168755200) = (499309866687:ℝ)/225162351544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4070
  · change lowerPayment 4071 ≤ lowerValue ((point 2 split 4096 4071+point 2 split 4096 4072)/2)
    have hp : lowerPayment 4071 = (421794593183:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4071+point 2 split 4096 4072)/2 = (574724133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574724133:ℝ)/168755200)/ClassicalSixthBranch.v ((574724133:ℝ)/168755200) = (499232553013:ℝ)/225114343656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4071
  · change lowerPayment 4072 ≤ lowerValue ((point 2 split 4096 4072+point 2 split 4096 4073)/2)
    have hp : lowerPayment 4072 = (421896821963:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4072+point 2 split 4096 4073)/2 = (114956479:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114956479:ℝ)/33751040)/ClassicalSixthBranch.v ((114956479:ℝ)/33751040) = (499155239339:ℝ)/225066335768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4072
  · change lowerPayment 4073 ≤ lowerValue ((point 2 split 4096 4073+point 2 split 4096 4074)/2)
    have hp : lowerPayment 4073 = (421999072636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4073+point 2 split 4096 4074)/2 = (574840657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574840657:ℝ)/168755200)/ClassicalSixthBranch.v ((574840657:ℝ)/168755200) = (99815585133:ℝ)/45003665576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4073
  · change lowerPayment 4074 ≤ lowerValue ((point 2 split 4096 4074+point 2 split 4096 4075)/2)
    have hp : lowerPayment 4074 = (422101345223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4074+point 2 split 4096 4075)/2 = (574898919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574898919:ℝ)/168755200)/ClassicalSixthBranch.v ((574898919:ℝ)/168755200) = (499000611991:ℝ)/224970319992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4074
  · change lowerPayment 4075 ≤ lowerValue ((point 2 split 4096 4075+point 2 split 4096 4076)/2)
    have hp : lowerPayment 4075 = (422203639742:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4075+point 2 split 4096 4076)/2 = (574957181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574957181:ℝ)/168755200)/ClassicalSixthBranch.v ((574957181:ℝ)/168755200) = (498923298317:ℝ)/224922312104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4075
  · change lowerPayment 4076 ≤ lowerValue ((point 2 split 4096 4076+point 2 split 4096 4077)/2)
    have hp : lowerPayment 4076 = (422305956214:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4076+point 2 split 4096 4077)/2 = (575015443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575015443:ℝ)/168755200)/ClassicalSixthBranch.v ((575015443:ℝ)/168755200) = (498845984643:ℝ)/224874304216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4076
  · change lowerPayment 4077 ≤ lowerValue ((point 2 split 4096 4077+point 2 split 4096 4078)/2)
    have hp : lowerPayment 4077 = (422408294657:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4077+point 2 split 4096 4078)/2 = (115014741:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((115014741:ℝ)/33751040)/ClassicalSixthBranch.v ((115014741:ℝ)/33751040) = (498768670969:ℝ)/224826296328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4077
  · change lowerPayment 4078 ≤ lowerValue ((point 2 split 4096 4078+point 2 split 4096 4079)/2)
    have hp : lowerPayment 4078 = (422510655093:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4078+point 2 split 4096 4079)/2 = (575131967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575131967:ℝ)/168755200)/ClassicalSixthBranch.v ((575131967:ℝ)/168755200) = (99738271459:ℝ)/44955657688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4078
  · change lowerPayment 4079 ≤ lowerValue ((point 2 split 4096 4079+point 2 split 4096 4080)/2)
    have hp : lowerPayment 4079 = (422613037539:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4079+point 2 split 4096 4080)/2 = (575190229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575190229:ℝ)/168755200)/ClassicalSixthBranch.v ((575190229:ℝ)/168755200) = (498614043621:ℝ)/224730280552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4079
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_254
