import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints196
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_196 (j : Fin 16) : lowerPayment (16*196+j.val) ≤
    lowerValue ((point 2 split 4096 (16*196+j.val)+point 2 split 4096 (16*196+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3136 ≤ lowerValue ((point 2 split 4096 3136+point 2 split 4096 3137)/2)
    have hp : lowerPayment 3136 = (333371672251:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3136+point 2 split 4096 3137)/2 = (520249163:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520249163:ℝ)/168755200)/ClassicalSixthBranch.v ((520249163:ℝ)/168755200) = (571520838203:ℝ)/270001718936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3136
  · change lowerPayment 3137 ≤ lowerValue ((point 2 split 4096 3137+point 2 split 4096 3138)/2)
    have hp : lowerPayment 3137 = (333460960316:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3137+point 2 split 4096 3138)/2 = (20812297:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20812297:ℝ)/6750208)/ClassicalSixthBranch.v ((20812297:ℝ)/6750208) = (571443524529:ℝ)/269953711048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3137
  · change lowerPayment 3138 ≤ lowerValue ((point 2 split 4096 3138+point 2 split 4096 3139)/2)
    have hp : lowerPayment 3138 = (333550254989:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3138+point 2 split 4096 3139)/2 = (520365687:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520365687:ℝ)/168755200)/ClassicalSixthBranch.v ((520365687:ℝ)/168755200) = (114273242171:ℝ)/53981140632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3138
  · change lowerPayment 3139 ≤ lowerValue ((point 2 split 4096 3139+point 2 split 4096 3140)/2)
    have hp : lowerPayment 3139 = (333639556285:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3139+point 2 split 4096 3140)/2 = (520423949:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520423949:ℝ)/168755200)/ClassicalSixthBranch.v ((520423949:ℝ)/168755200) = (571288897181:ℝ)/269857695272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3139
  · change lowerPayment 3140 ≤ lowerValue ((point 2 split 4096 3140+point 2 split 4096 3141)/2)
    have hp : lowerPayment 3140 = (333728864219:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3140+point 2 split 4096 3141)/2 = (520482211:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520482211:ℝ)/168755200)/ClassicalSixthBranch.v ((520482211:ℝ)/168755200) = (571211583507:ℝ)/269809687384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3140
  · change lowerPayment 3141 ≤ lowerValue ((point 2 split 4096 3141+point 2 split 4096 3142)/2)
    have hp : lowerPayment 3141 = (333818178804:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3141+point 2 split 4096 3142)/2 = (5053791:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((5053791:ℝ)/1638400)/ClassicalSixthBranch.v ((5053791:ℝ)/1638400) = (5544992911:ℝ)/2619045432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3141
  · change lowerPayment 3142 ≤ lowerValue ((point 2 split 4096 3142+point 2 split 4096 3143)/2)
    have hp : lowerPayment 3142 = (333907500055:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3142+point 2 split 4096 3143)/2 = (104119747:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104119747:ℝ)/33751040)/ClassicalSixthBranch.v ((104119747:ℝ)/33751040) = (571056956159:ℝ)/269713671608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3142
  · change lowerPayment 3143 ≤ lowerValue ((point 2 split 4096 3143+point 2 split 4096 3144)/2)
    have hp : lowerPayment 3143 = (333996827987:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3143+point 2 split 4096 3144)/2 = (520656997:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520656997:ℝ)/168755200)/ClassicalSixthBranch.v ((520656997:ℝ)/168755200) = (114195928497:ℝ)/53933132744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3143
  · change lowerPayment 3144 ≤ lowerValue ((point 2 split 4096 3144+point 2 split 4096 3145)/2)
    have hp : lowerPayment 3144 = (334086162613:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3144+point 2 split 4096 3145)/2 = (520715259:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520715259:ℝ)/168755200)/ClassicalSixthBranch.v ((520715259:ℝ)/168755200) = (570902328811:ℝ)/269617655832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3144
  · change lowerPayment 3145 ≤ lowerValue ((point 2 split 4096 3145+point 2 split 4096 3146)/2)
    have hp : lowerPayment 3145 = (334175503948:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3145+point 2 split 4096 3146)/2 = (520773521:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520773521:ℝ)/168755200)/ClassicalSixthBranch.v ((520773521:ℝ)/168755200) = (570825015137:ℝ)/269569647944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3145
  · change lowerPayment 3146 ≤ lowerValue ((point 2 split 4096 3146+point 2 split 4096 3147)/2)
    have hp : lowerPayment 3146 = (334264852007:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3146+point 2 split 4096 3147)/2 = (520831783:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520831783:ℝ)/168755200)/ClassicalSixthBranch.v ((520831783:ℝ)/168755200) = (570747701463:ℝ)/269521640056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3146
  · change lowerPayment 3147 ≤ lowerValue ((point 2 split 4096 3147+point 2 split 4096 3148)/2)
    have hp : lowerPayment 3147 = (334354206803:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3147+point 2 split 4096 3148)/2 = (104178009:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104178009:ℝ)/33751040)/ClassicalSixthBranch.v ((104178009:ℝ)/33751040) = (570670387789:ℝ)/269473632168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3147
  · change lowerPayment 3148 ≤ lowerValue ((point 2 split 4096 3148+point 2 split 4096 3149)/2)
    have hp : lowerPayment 3148 = (334443568352:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3148+point 2 split 4096 3149)/2 = (520948307:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520948307:ℝ)/168755200)/ClassicalSixthBranch.v ((520948307:ℝ)/168755200) = (114118614823:ℝ)/53885124856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3148
  · change lowerPayment 3149 ≤ lowerValue ((point 2 split 4096 3149+point 2 split 4096 3150)/2)
    have hp : lowerPayment 3149 = (334532936667:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3149+point 2 split 4096 3150)/2 = (521006569:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521006569:ℝ)/168755200)/ClassicalSixthBranch.v ((521006569:ℝ)/168755200) = (570515760441:ℝ)/269377616392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3149
  · change lowerPayment 3150 ≤ lowerValue ((point 2 split 4096 3150+point 2 split 4096 3151)/2)
    have hp : lowerPayment 3150 = (334622311764:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3150+point 2 split 4096 3151)/2 = (521064831:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521064831:ℝ)/168755200)/ClassicalSixthBranch.v ((521064831:ℝ)/168755200) = (570438446767:ℝ)/269329608504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3150
  · change lowerPayment 3151 ≤ lowerValue ((point 2 split 4096 3151+point 2 split 4096 3152)/2)
    have hp : lowerPayment 3151 = (334711693656:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3151+point 2 split 4096 3152)/2 = (521123093:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521123093:ℝ)/168755200)/ClassicalSixthBranch.v ((521123093:ℝ)/168755200) = (570361133093:ℝ)/269281600616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3151
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_196
