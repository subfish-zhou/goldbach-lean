import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints223
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_223 (j : Fin 16) : lowerPayment (16*223+j.val) ≤
    lowerValue ((point 2 split 4096 (16*223+j.val)+point 2 split 4096 (16*223+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3568 ≤ lowerValue ((point 2 split 4096 3568+point 2 split 4096 3569)/2)
    have hp : lowerPayment 3568 = (372754560346:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3568+point 2 split 4096 3569)/2 = (545418347:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545418347:ℝ)/168755200)/ClassicalSixthBranch.v ((545418347:ℝ)/168755200) = (107624266207:ℝ)/49852462264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3568
  · change lowerPayment 3569 ≤ lowerValue ((point 2 split 4096 3569+point 2 split 4096 3570)/2)
    have hp : lowerPayment 3569 = (372848075690:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3569+point 2 split 4096 3570)/2 = (545476609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545476609:ℝ)/168755200)/ClassicalSixthBranch.v ((545476609:ℝ)/168755200) = (538044017361:ℝ)/249214303432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3569
  · change lowerPayment 3570 ≤ lowerValue ((point 2 split 4096 3570+point 2 split 4096 3571)/2)
    have hp : lowerPayment 3570 = (372941604117:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3570+point 2 split 4096 3571)/2 = (545534871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545534871:ℝ)/168755200)/ClassicalSixthBranch.v ((545534871:ℝ)/168755200) = (537966703687:ℝ)/249166295544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3570
  · change lowerPayment 3571 ≤ lowerValue ((point 2 split 4096 3571+point 2 split 4096 3572)/2)
    have hp : lowerPayment 3571 = (373035145644:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3571+point 2 split 4096 3572)/2 = (545593133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545593133:ℝ)/168755200)/ClassicalSixthBranch.v ((545593133:ℝ)/168755200) = (537889390013:ℝ)/249118287656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3571
  · change lowerPayment 3572 ≤ lowerValue ((point 2 split 4096 3572+point 2 split 4096 3573)/2)
    have hp : lowerPayment 3572 = (373128700286:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3572+point 2 split 4096 3573)/2 = (109130279:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109130279:ℝ)/33751040)/ClassicalSixthBranch.v ((109130279:ℝ)/33751040) = (537812076339:ℝ)/249070279768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3572
  · change lowerPayment 3573 ≤ lowerValue ((point 2 split 4096 3573+point 2 split 4096 3574)/2)
    have hp : lowerPayment 3573 = (373222268060:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3573+point 2 split 4096 3574)/2 = (545709657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545709657:ℝ)/168755200)/ClassicalSixthBranch.v ((545709657:ℝ)/168755200) = (107546952533:ℝ)/49804454376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3573
  · change lowerPayment 3574 ≤ lowerValue ((point 2 split 4096 3574+point 2 split 4096 3575)/2)
    have hp : lowerPayment 3574 = (373315848980:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3574+point 2 split 4096 3575)/2 = (545767919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545767919:ℝ)/168755200)/ClassicalSixthBranch.v ((545767919:ℝ)/168755200) = (537657448991:ℝ)/248974263992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3574
  · change lowerPayment 3575 ≤ lowerValue ((point 2 split 4096 3575+point 2 split 4096 3576)/2)
    have hp : lowerPayment 3575 = (373409443064:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3575+point 2 split 4096 3576)/2 = (545826181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545826181:ℝ)/168755200)/ClassicalSixthBranch.v ((545826181:ℝ)/168755200) = (537580135317:ℝ)/248926256104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3575
  · change lowerPayment 3576 ≤ lowerValue ((point 2 split 4096 3576+point 2 split 4096 3577)/2)
    have hp : lowerPayment 3576 = (373503050327:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3576+point 2 split 4096 3577)/2 = (545884443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545884443:ℝ)/168755200)/ClassicalSixthBranch.v ((545884443:ℝ)/168755200) = (537502821643:ℝ)/248878248216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3576
  · change lowerPayment 3577 ≤ lowerValue ((point 2 split 4096 3577+point 2 split 4096 3578)/2)
    have hp : lowerPayment 3577 = (373596670784:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3577+point 2 split 4096 3578)/2 = (109188541:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109188541:ℝ)/33751040)/ClassicalSixthBranch.v ((109188541:ℝ)/33751040) = (537425507969:ℝ)/248830240328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3577
  · change lowerPayment 3578 ≤ lowerValue ((point 2 split 4096 3578+point 2 split 4096 3579)/2)
    have hp : lowerPayment 3578 = (373690304452:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3578+point 2 split 4096 3579)/2 = (546000967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546000967:ℝ)/168755200)/ClassicalSixthBranch.v ((546000967:ℝ)/168755200) = (107469638859:ℝ)/49756446488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3578
  · change lowerPayment 3579 ≤ lowerValue ((point 2 split 4096 3579+point 2 split 4096 3580)/2)
    have hp : lowerPayment 3579 = (373783951346:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3579+point 2 split 4096 3580)/2 = (546059229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546059229:ℝ)/168755200)/ClassicalSixthBranch.v ((546059229:ℝ)/168755200) = (537270880621:ℝ)/248734224552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3579
  · change lowerPayment 3580 ≤ lowerValue ((point 2 split 4096 3580+point 2 split 4096 3581)/2)
    have hp : lowerPayment 3580 = (373877611483:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3580+point 2 split 4096 3581)/2 = (546117491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546117491:ℝ)/168755200)/ClassicalSixthBranch.v ((546117491:ℝ)/168755200) = (537193566947:ℝ)/248686216664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3580
  · change lowerPayment 3581 ≤ lowerValue ((point 2 split 4096 3581+point 2 split 4096 3582)/2)
    have hp : lowerPayment 3581 = (373971284878:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3581+point 2 split 4096 3582)/2 = (546175753:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546175753:ℝ)/168755200)/ClassicalSixthBranch.v ((546175753:ℝ)/168755200) = (537116253273:ℝ)/248638208776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3581
  · change lowerPayment 3582 ≤ lowerValue ((point 2 split 4096 3582+point 2 split 4096 3583)/2)
    have hp : lowerPayment 3582 = (374064971547:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3582+point 2 split 4096 3583)/2 = (109246803:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109246803:ℝ)/33751040)/ClassicalSixthBranch.v ((109246803:ℝ)/33751040) = (537038939599:ℝ)/248590200888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3582
  · change lowerPayment 3583 ≤ lowerValue ((point 2 split 4096 3583+point 2 split 4096 3584)/2)
    have hp : lowerPayment 3583 = (374158671507:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3583+point 2 split 4096 3584)/2 = (546292277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546292277:ℝ)/168755200)/ClassicalSixthBranch.v ((546292277:ℝ)/168755200) = (21478465037:ℝ)/9941687720 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3583
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_223
