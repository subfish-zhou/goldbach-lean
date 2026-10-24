import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints000
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_000 (j : Fin 16) : lowerPayment (16*0+j.val) ≤
    lowerValue ((point 2 split 4096 (16*0+j.val)+point 2 split 4096 (16*0+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 0 ≤ lowerValue ((point 2 split 4096 0+point 2 split 4096 1)/2)
    have hp : lowerPayment 0 = (81579263:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 0+point 2 split 4096 1)/2 = (337539531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((337539531:ℝ)/168755200)/ClassicalSixthBranch.v ((337539531:ℝ)/168755200) = (813976519867:ℝ)/420554455704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_0
  · change lowerPayment 1 ≤ lowerValue ((point 2 split 4096 1+point 2 split 4096 2)/2)
    have hp : lowerPayment 1 = (244678657:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1+point 2 split 4096 2)/2 = (337597793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((337597793:ℝ)/168755200)/ClassicalSixthBranch.v ((337597793:ℝ)/168755200) = (813899206193:ℝ)/420506447816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1
  · change lowerPayment 2 ≤ lowerValue ((point 2 split 4096 2+point 2 split 4096 3)/2)
    have hp : lowerPayment 2 = (407699271:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2+point 2 split 4096 3)/2 = (67531211:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((67531211:ℝ)/33751040)/ClassicalSixthBranch.v ((67531211:ℝ)/33751040) = (813821892519:ℝ)/420458439928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2
  · change lowerPayment 3 ≤ lowerValue ((point 2 split 4096 3+point 2 split 4096 4)/2)
    have hp : lowerPayment 3 = (570641176:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3+point 2 split 4096 4)/2 = (337714317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((337714317:ℝ)/168755200)/ClassicalSixthBranch.v ((337714317:ℝ)/168755200) = (162748915769:ℝ)/84082086408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3
  · change lowerPayment 4 ≤ lowerValue ((point 2 split 4096 4+point 2 split 4096 5)/2)
    have hp : lowerPayment 4 = (733504446:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4+point 2 split 4096 5)/2 = (337772579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((337772579:ℝ)/168755200)/ClassicalSixthBranch.v ((337772579:ℝ)/168755200) = (813667265171:ℝ)/420362424152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4
  · change lowerPayment 5 ≤ lowerValue ((point 2 split 4096 5+point 2 split 4096 6)/2)
    have hp : lowerPayment 5 = (896289151:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 5+point 2 split 4096 6)/2 = (337830841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((337830841:ℝ)/168755200)/ClassicalSixthBranch.v ((337830841:ℝ)/168755200) = (813589951497:ℝ)/420314416264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_5
  · change lowerPayment 6 ≤ lowerValue ((point 2 split 4096 6+point 2 split 4096 7)/2)
    have hp : lowerPayment 6 = (1058995366:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 6+point 2 split 4096 7)/2 = (337889103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((337889103:ℝ)/168755200)/ClassicalSixthBranch.v ((337889103:ℝ)/168755200) = (813512637823:ℝ)/420266408376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_6
  · change lowerPayment 7 ≤ lowerValue ((point 2 split 4096 7+point 2 split 4096 8)/2)
    have hp : lowerPayment 7 = (1221623162:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 7+point 2 split 4096 8)/2 = (67589473:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((67589473:ℝ)/33751040)/ClassicalSixthBranch.v ((67589473:ℝ)/33751040) = (813435324149:ℝ)/420218400488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_7
  · change lowerPayment 8 ≤ lowerValue ((point 2 split 4096 8+point 2 split 4096 9)/2)
    have hp : lowerPayment 8 = (1384172611:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 8+point 2 split 4096 9)/2 = (338005627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338005627:ℝ)/168755200)/ClassicalSixthBranch.v ((338005627:ℝ)/168755200) = (32534320419:ℝ)/16806815704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_8
  · change lowerPayment 9 ≤ lowerValue ((point 2 split 4096 9+point 2 split 4096 10)/2)
    have hp : lowerPayment 9 = (1546643786:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 9+point 2 split 4096 10)/2 = (338063889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338063889:ℝ)/168755200)/ClassicalSixthBranch.v ((338063889:ℝ)/168755200) = (813280696801:ℝ)/420122384712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_9
  · change lowerPayment 10 ≤ lowerValue ((point 2 split 4096 10+point 2 split 4096 11)/2)
    have hp : lowerPayment 10 = (1709036759:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 10+point 2 split 4096 11)/2 = (338122151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338122151:ℝ)/168755200)/ClassicalSixthBranch.v ((338122151:ℝ)/168755200) = (813203383127:ℝ)/420074376824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_10
  · change lowerPayment 11 ≤ lowerValue ((point 2 split 4096 11+point 2 split 4096 12)/2)
    have hp : lowerPayment 11 = (1871351601:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 11+point 2 split 4096 12)/2 = (338180413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338180413:ℝ)/168755200)/ClassicalSixthBranch.v ((338180413:ℝ)/168755200) = (813126069453:ℝ)/420026368936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_11
  · change lowerPayment 12 ≤ lowerValue ((point 2 split 4096 12+point 2 split 4096 13)/2)
    have hp : lowerPayment 12 = (2033588385:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 12+point 2 split 4096 13)/2 = (13529547:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13529547:ℝ)/6750208)/ClassicalSixthBranch.v ((13529547:ℝ)/6750208) = (813048755779:ℝ)/419978361048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_12
  · change lowerPayment 13 ≤ lowerValue ((point 2 split 4096 13+point 2 split 4096 14)/2)
    have hp : lowerPayment 13 = (2195747183:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 13+point 2 split 4096 14)/2 = (338296937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338296937:ℝ)/168755200)/ClassicalSixthBranch.v ((338296937:ℝ)/168755200) = (162594288421:ℝ)/83986070632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_13
  · change lowerPayment 14 ≤ lowerValue ((point 2 split 4096 14+point 2 split 4096 15)/2)
    have hp : lowerPayment 14 = (2357828065:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 14+point 2 split 4096 15)/2 = (338355199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338355199:ℝ)/168755200)/ClassicalSixthBranch.v ((338355199:ℝ)/168755200) = (812894128431:ℝ)/419882345272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_14
  · change lowerPayment 15 ≤ lowerValue ((point 2 split 4096 15+point 2 split 4096 16)/2)
    have hp : lowerPayment 15 = (2519831105:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 15+point 2 split 4096 16)/2 = (338413461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338413461:ℝ)/168755200)/ClassicalSixthBranch.v ((338413461:ℝ)/168755200) = (812816814757:ℝ)/419834337384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_15
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_000
