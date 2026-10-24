import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints199
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_199 (j : Fin 16) : lowerPayment (16*199+j.val) ≤
    lowerValue ((point 2 split 4096 (16*199+j.val)+point 2 split 4096 (16*199+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3184 ≤ lowerValue ((point 2 split 4096 3184+point 2 split 4096 3185)/2)
    have hp : lowerPayment 3184 = (337665202576:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3184+point 2 split 4096 3185)/2 = (523045739:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523045739:ℝ)/168755200)/ClassicalSixthBranch.v ((523045739:ℝ)/168755200) = (567809781851:ℝ)/267697340312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3184
  · change lowerPayment 3185 ≤ lowerValue ((point 2 split 4096 3185+point 2 split 4096 3186)/2)
    have hp : lowerPayment 3185 = (337754824085:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3185+point 2 split 4096 3186)/2 = (523104001:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523104001:ℝ)/168755200)/ClassicalSixthBranch.v ((523104001:ℝ)/168755200) = (567732468177:ℝ)/267649332424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3185
  · change lowerPayment 3186 ≤ lowerValue ((point 2 split 4096 3186+point 2 split 4096 3187)/2)
    have hp : lowerPayment 3186 = (337844452895:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3186+point 2 split 4096 3187)/2 = (523162263:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523162263:ℝ)/168755200)/ClassicalSixthBranch.v ((523162263:ℝ)/168755200) = (567655154503:ℝ)/267601324536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3186
  · change lowerPayment 3187 ≤ lowerValue ((point 2 split 4096 3187+point 2 split 4096 3188)/2)
    have hp : lowerPayment 3187 = (337934089019:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3187+point 2 split 4096 3188)/2 = (20928821:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20928821:ℝ)/6750208)/ClassicalSixthBranch.v ((20928821:ℝ)/6750208) = (567577840829:ℝ)/267553316648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3187
  · change lowerPayment 3188 ≤ lowerValue ((point 2 split 4096 3188+point 2 split 4096 3189)/2)
    have hp : lowerPayment 3188 = (338023732473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3188+point 2 split 4096 3189)/2 = (523278787:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523278787:ℝ)/168755200)/ClassicalSixthBranch.v ((523278787:ℝ)/168755200) = (113500105431:ℝ)/53501061752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3188
  · change lowerPayment 3189 ≤ lowerValue ((point 2 split 4096 3189+point 2 split 4096 3190)/2)
    have hp : lowerPayment 3189 = (338113383270:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3189+point 2 split 4096 3190)/2 = (523337049:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523337049:ℝ)/168755200)/ClassicalSixthBranch.v ((523337049:ℝ)/168755200) = (567423213481:ℝ)/267457300872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3189
  · change lowerPayment 3190 ≤ lowerValue ((point 2 split 4096 3190+point 2 split 4096 3191)/2)
    have hp : lowerPayment 3190 = (338203041425:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3190+point 2 split 4096 3191)/2 = (523395311:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523395311:ℝ)/168755200)/ClassicalSixthBranch.v ((523395311:ℝ)/168755200) = (567345899807:ℝ)/267409292984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3190
  · change lowerPayment 3191 ≤ lowerValue ((point 2 split 4096 3191+point 2 split 4096 3192)/2)
    have hp : lowerPayment 3191 = (338292706953:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3191+point 2 split 4096 3192)/2 = (523453573:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523453573:ℝ)/168755200)/ClassicalSixthBranch.v ((523453573:ℝ)/168755200) = (567268586133:ℝ)/267361285096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3191
  · change lowerPayment 3192 ≤ lowerValue ((point 2 split 4096 3192+point 2 split 4096 3193)/2)
    have hp : lowerPayment 3192 = (338382379868:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3192+point 2 split 4096 3193)/2 = (104702367:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104702367:ℝ)/33751040)/ClassicalSixthBranch.v ((104702367:ℝ)/33751040) = (567191272459:ℝ)/267313277208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3192
  · change lowerPayment 3193 ≤ lowerValue ((point 2 split 4096 3193+point 2 split 4096 3194)/2)
    have hp : lowerPayment 3193 = (338472060184:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3193+point 2 split 4096 3194)/2 = (523570097:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523570097:ℝ)/168755200)/ClassicalSixthBranch.v ((523570097:ℝ)/168755200) = (113422791757:ℝ)/53453053864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3193
  · change lowerPayment 3194 ≤ lowerValue ((point 2 split 4096 3194+point 2 split 4096 3195)/2)
    have hp : lowerPayment 3194 = (338561747916:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3194+point 2 split 4096 3195)/2 = (523628359:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523628359:ℝ)/168755200)/ClassicalSixthBranch.v ((523628359:ℝ)/168755200) = (567036645111:ℝ)/267217261432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3194
  · change lowerPayment 3195 ≤ lowerValue ((point 2 split 4096 3195+point 2 split 4096 3196)/2)
    have hp : lowerPayment 3195 = (338651443079:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3195+point 2 split 4096 3196)/2 = (523686621:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523686621:ℝ)/168755200)/ClassicalSixthBranch.v ((523686621:ℝ)/168755200) = (566959331437:ℝ)/267169253544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3195
  · change lowerPayment 3196 ≤ lowerValue ((point 2 split 4096 3196+point 2 split 4096 3197)/2)
    have hp : lowerPayment 3196 = (338741145687:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3196+point 2 split 4096 3197)/2 = (523744883:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523744883:ℝ)/168755200)/ClassicalSixthBranch.v ((523744883:ℝ)/168755200) = (566882017763:ℝ)/267121245656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3196
  · change lowerPayment 3197 ≤ lowerValue ((point 2 split 4096 3197+point 2 split 4096 3198)/2)
    have hp : lowerPayment 3197 = (338830855754:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3197+point 2 split 4096 3198)/2 = (104760629:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104760629:ℝ)/33751040)/ClassicalSixthBranch.v ((104760629:ℝ)/33751040) = (566804704089:ℝ)/267073237768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3197
  · change lowerPayment 3198 ≤ lowerValue ((point 2 split 4096 3198+point 2 split 4096 3199)/2)
    have hp : lowerPayment 3198 = (338920573295:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3198+point 2 split 4096 3199)/2 = (523861407:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523861407:ℝ)/168755200)/ClassicalSixthBranch.v ((523861407:ℝ)/168755200) = (113345478083:ℝ)/53405045976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3198
  · change lowerPayment 3199 ≤ lowerValue ((point 2 split 4096 3199+point 2 split 4096 3200)/2)
    have hp : lowerPayment 3199 = (339010298324:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3199+point 2 split 4096 3200)/2 = (523919669:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((523919669:ℝ)/168755200)/ClassicalSixthBranch.v ((523919669:ℝ)/168755200) = (566650076741:ℝ)/266977221992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3199
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_199
