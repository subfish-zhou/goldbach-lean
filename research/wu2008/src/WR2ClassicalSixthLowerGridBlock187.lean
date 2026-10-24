import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints187
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_187 (j : Fin 16) : lowerPayment (16*187+j.val) ≤
    lowerValue ((point 2 split 4096 (16*187+j.val)+point 2 split 4096 (16*187+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2992 ≤ lowerValue ((point 2 split 4096 2992+point 2 split 4096 2993)/2)
    have hp : lowerPayment 2992 = (320575916752:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2992+point 2 split 4096 2993)/2 = (102371887:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102371887:ℝ)/33751040)/ClassicalSixthBranch.v ((102371887:ℝ)/33751040) = (582654007259:ℝ)/276914854808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2992
  · change lowerPayment 2993 ≤ lowerValue ((point 2 split 4096 2993+point 2 split 4096 2994)/2)
    have hp : lowerPayment 2993 = (320664402329:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2993+point 2 split 4096 2994)/2 = (511917697:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511917697:ℝ)/168755200)/ClassicalSixthBranch.v ((511917697:ℝ)/168755200) = (116515338717:ℝ)/55373369384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2993
  · change lowerPayment 2994 ≤ lowerValue ((point 2 split 4096 2994+point 2 split 4096 2995)/2)
    have hp : lowerPayment 2994 = (320752892462:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2994+point 2 split 4096 2995)/2 = (511975959:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511975959:ℝ)/168755200)/ClassicalSixthBranch.v ((511975959:ℝ)/168755200) = (582499379911:ℝ)/276818839032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2994
  · change lowerPayment 2995 ≤ lowerValue ((point 2 split 4096 2995+point 2 split 4096 2996)/2)
    have hp : lowerPayment 2995 = (320841387166:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2995+point 2 split 4096 2996)/2 = (512034221:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512034221:ℝ)/168755200)/ClassicalSixthBranch.v ((512034221:ℝ)/168755200) = (582422066237:ℝ)/276770831144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2995
  · change lowerPayment 2996 ≤ lowerValue ((point 2 split 4096 2996+point 2 split 4096 2997)/2)
    have hp : lowerPayment 2996 = (320929886454:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2996+point 2 split 4096 2997)/2 = (512092483:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512092483:ℝ)/168755200)/ClassicalSixthBranch.v ((512092483:ℝ)/168755200) = (582344752563:ℝ)/276722823256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2996
  · change lowerPayment 2997 ≤ lowerValue ((point 2 split 4096 2997+point 2 split 4096 2998)/2)
    have hp : lowerPayment 2997 = (321018390340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2997+point 2 split 4096 2998)/2 = (102430149:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102430149:ℝ)/33751040)/ClassicalSixthBranch.v ((102430149:ℝ)/33751040) = (582267438889:ℝ)/276674815368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2997
  · change lowerPayment 2998 ≤ lowerValue ((point 2 split 4096 2998+point 2 split 4096 2999)/2)
    have hp : lowerPayment 2998 = (321106898840:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2998+point 2 split 4096 2999)/2 = (512209007:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512209007:ℝ)/168755200)/ClassicalSixthBranch.v ((512209007:ℝ)/168755200) = (116438025043:ℝ)/55325361496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2998
  · change lowerPayment 2999 ≤ lowerValue ((point 2 split 4096 2999+point 2 split 4096 3000)/2)
    have hp : lowerPayment 2999 = (321195411967:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2999+point 2 split 4096 3000)/2 = (512267269:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512267269:ℝ)/168755200)/ClassicalSixthBranch.v ((512267269:ℝ)/168755200) = (582112811541:ℝ)/276578799592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2999
  · change lowerPayment 3000 ≤ lowerValue ((point 2 split 4096 3000+point 2 split 4096 3001)/2)
    have hp : lowerPayment 3000 = (321283929734:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3000+point 2 split 4096 3001)/2 = (512325531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512325531:ℝ)/168755200)/ClassicalSixthBranch.v ((512325531:ℝ)/168755200) = (582035497867:ℝ)/276530791704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3000
  · change lowerPayment 3001 ≤ lowerValue ((point 2 split 4096 3001+point 2 split 4096 3002)/2)
    have hp : lowerPayment 3001 = (321372452157:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3001+point 2 split 4096 3002)/2 = (512383793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512383793:ℝ)/168755200)/ClassicalSixthBranch.v ((512383793:ℝ)/168755200) = (581958184193:ℝ)/276482783816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3001
  · change lowerPayment 3002 ≤ lowerValue ((point 2 split 4096 3002+point 2 split 4096 3003)/2)
    have hp : lowerPayment 3002 = (321460979250:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3002+point 2 split 4096 3003)/2 = (102488411:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102488411:ℝ)/33751040)/ClassicalSixthBranch.v ((102488411:ℝ)/33751040) = (581880870519:ℝ)/276434775928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3002
  · change lowerPayment 3003 ≤ lowerValue ((point 2 split 4096 3003+point 2 split 4096 3004)/2)
    have hp : lowerPayment 3003 = (321549511026:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3003+point 2 split 4096 3004)/2 = (512500317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512500317:ℝ)/168755200)/ClassicalSixthBranch.v ((512500317:ℝ)/168755200) = (116360711369:ℝ)/55277353608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3003
  · change lowerPayment 3004 ≤ lowerValue ((point 2 split 4096 3004+point 2 split 4096 3005)/2)
    have hp : lowerPayment 3004 = (321638047501:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3004+point 2 split 4096 3005)/2 = (512558579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512558579:ℝ)/168755200)/ClassicalSixthBranch.v ((512558579:ℝ)/168755200) = (581726243171:ℝ)/276338760152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3004
  · change lowerPayment 3005 ≤ lowerValue ((point 2 split 4096 3005+point 2 split 4096 3006)/2)
    have hp : lowerPayment 3005 = (321726588687:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3005+point 2 split 4096 3006)/2 = (512616841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512616841:ℝ)/168755200)/ClassicalSixthBranch.v ((512616841:ℝ)/168755200) = (581648929497:ℝ)/276290752264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3005
  · change lowerPayment 3006 ≤ lowerValue ((point 2 split 4096 3006+point 2 split 4096 3007)/2)
    have hp : lowerPayment 3006 = (321815134599:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3006+point 2 split 4096 3007)/2 = (512675103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((512675103:ℝ)/168755200)/ClassicalSixthBranch.v ((512675103:ℝ)/168755200) = (581571615823:ℝ)/276242744376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3006
  · change lowerPayment 3007 ≤ lowerValue ((point 2 split 4096 3007+point 2 split 4096 3008)/2)
    have hp : lowerPayment 3007 = (321903685252:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3007+point 2 split 4096 3008)/2 = (102546673:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102546673:ℝ)/33751040)/ClassicalSixthBranch.v ((102546673:ℝ)/33751040) = (581494302149:ℝ)/276194736488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3007
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_187
