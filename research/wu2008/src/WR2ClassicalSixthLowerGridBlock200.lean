import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints200
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_200 (j : Fin 16) : lowerPayment (16*200+j.val) ≤
    lowerValue ((point 2 split 4096 (16*200+j.val)+point 2 split 4096 (16*200+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3200 ≤ lowerValue ((point 2 split 4096 3200+point 2 split 4096 3201)/2)
    have hp : lowerPayment 3200 = (339100030857:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3200+point 2 split 4096 3201)/2 = (523977931:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523977931:ℝ)/168755200)/ClassicalSixthBranch.v ((523977931:ℝ)/168755200) = (566572763067:ℝ)/266929214104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3200
  · change lowerPayment 3201 ≤ lowerValue ((point 2 split 4096 3201+point 2 split 4096 3202)/2)
    have hp : lowerPayment 3201 = (339189770906:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3201+point 2 split 4096 3202)/2 = (524036193:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524036193:ℝ)/168755200)/ClassicalSixthBranch.v ((524036193:ℝ)/168755200) = (566495449393:ℝ)/266881206216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3201
  · change lowerPayment 3202 ≤ lowerValue ((point 2 split 4096 3202+point 2 split 4096 3203)/2)
    have hp : lowerPayment 3202 = (339279518488:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3202+point 2 split 4096 3203)/2 = (104818891:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104818891:ℝ)/33751040)/ClassicalSixthBranch.v ((104818891:ℝ)/33751040) = (566418135719:ℝ)/266833198328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3202
  · change lowerPayment 3203 ≤ lowerValue ((point 2 split 4096 3203+point 2 split 4096 3204)/2)
    have hp : lowerPayment 3203 = (339369273616:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3203+point 2 split 4096 3204)/2 = (524152717:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524152717:ℝ)/168755200)/ClassicalSixthBranch.v ((524152717:ℝ)/168755200) = (113268164409:ℝ)/53357038088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3203
  · change lowerPayment 3204 ≤ lowerValue ((point 2 split 4096 3204+point 2 split 4096 3205)/2)
    have hp : lowerPayment 3204 = (339459036305:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3204+point 2 split 4096 3205)/2 = (524210979:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524210979:ℝ)/168755200)/ClassicalSixthBranch.v ((524210979:ℝ)/168755200) = (566263508371:ℝ)/266737182552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3204
  · change lowerPayment 3205 ≤ lowerValue ((point 2 split 4096 3205+point 2 split 4096 3206)/2)
    have hp : lowerPayment 3205 = (339548806569:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3205+point 2 split 4096 3206)/2 = (524269241:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524269241:ℝ)/168755200)/ClassicalSixthBranch.v ((524269241:ℝ)/168755200) = (566186194697:ℝ)/266689174664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3205
  · change lowerPayment 3206 ≤ lowerValue ((point 2 split 4096 3206+point 2 split 4096 3207)/2)
    have hp : lowerPayment 3206 = (339638584423:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3206+point 2 split 4096 3207)/2 = (524327503:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524327503:ℝ)/168755200)/ClassicalSixthBranch.v ((524327503:ℝ)/168755200) = (566108881023:ℝ)/266641166776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3206
  · change lowerPayment 3207 ≤ lowerValue ((point 2 split 4096 3207+point 2 split 4096 3208)/2)
    have hp : lowerPayment 3207 = (339728369881:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3207+point 2 split 4096 3208)/2 = (104877153:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104877153:ℝ)/33751040)/ClassicalSixthBranch.v ((104877153:ℝ)/33751040) = (566031567349:ℝ)/266593158888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3207
  · change lowerPayment 3208 ≤ lowerValue ((point 2 split 4096 3208+point 2 split 4096 3209)/2)
    have hp : lowerPayment 3208 = (339818162959:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3208+point 2 split 4096 3209)/2 = (524444027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524444027:ℝ)/168755200)/ClassicalSixthBranch.v ((524444027:ℝ)/168755200) = (22638170147:ℝ)/10661806040 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3208
  · change lowerPayment 3209 ≤ lowerValue ((point 2 split 4096 3209+point 2 split 4096 3210)/2)
    have hp : lowerPayment 3209 = (339907963670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3209+point 2 split 4096 3210)/2 = (524502289:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524502289:ℝ)/168755200)/ClassicalSixthBranch.v ((524502289:ℝ)/168755200) = (565876940001:ℝ)/266497143112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3209
  · change lowerPayment 3210 ≤ lowerValue ((point 2 split 4096 3210+point 2 split 4096 3211)/2)
    have hp : lowerPayment 3210 = (339997772028:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3210+point 2 split 4096 3211)/2 = (524560551:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524560551:ℝ)/168755200)/ClassicalSixthBranch.v ((524560551:ℝ)/168755200) = (565799626327:ℝ)/266449135224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3210
  · change lowerPayment 3211 ≤ lowerValue ((point 2 split 4096 3211+point 2 split 4096 3212)/2)
    have hp : lowerPayment 3211 = (340087588049:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3211+point 2 split 4096 3212)/2 = (524618813:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524618813:ℝ)/168755200)/ClassicalSixthBranch.v ((524618813:ℝ)/168755200) = (565722312653:ℝ)/266401127336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3211
  · change lowerPayment 3212 ≤ lowerValue ((point 2 split 4096 3212+point 2 split 4096 3213)/2)
    have hp : lowerPayment 3212 = (340177411747:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3212+point 2 split 4096 3213)/2 = (20987083:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20987083:ℝ)/6750208)/ClassicalSixthBranch.v ((20987083:ℝ)/6750208) = (565644998979:ℝ)/266353119448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3212
  · change lowerPayment 3213 ≤ lowerValue ((point 2 split 4096 3213+point 2 split 4096 3214)/2)
    have hp : lowerPayment 3213 = (340267243137:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3213+point 2 split 4096 3214)/2 = (524735337:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524735337:ℝ)/168755200)/ClassicalSixthBranch.v ((524735337:ℝ)/168755200) = (113113537061:ℝ)/53261022312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3213
  · change lowerPayment 3214 ≤ lowerValue ((point 2 split 4096 3214+point 2 split 4096 3215)/2)
    have hp : lowerPayment 3214 = (340357082233:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3214+point 2 split 4096 3215)/2 = (524793599:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524793599:ℝ)/168755200)/ClassicalSixthBranch.v ((524793599:ℝ)/168755200) = (565490371631:ℝ)/266257103672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3214
  · change lowerPayment 3215 ≤ lowerValue ((point 2 split 4096 3215+point 2 split 4096 3216)/2)
    have hp : lowerPayment 3215 = (340446929049:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3215+point 2 split 4096 3216)/2 = (524851861:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524851861:ℝ)/168755200)/ClassicalSixthBranch.v ((524851861:ℝ)/168755200) = (565413057957:ℝ)/266209095784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3215
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_200
