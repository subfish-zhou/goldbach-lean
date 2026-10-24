import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints170
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_170 (j : Fin 16) : lowerPayment (16*170+j.val) ≤
    lowerValue ((point 2 split 4096 (16*170+j.val)+point 2 split 4096 (16*170+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2720 ≤ lowerValue ((point 2 split 4096 2720+point 2 split 4096 2721)/2)
    have hp : lowerPayment 2720 = (296629092471:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2720+point 2 split 4096 2721)/2 = (496012171:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496012171:ℝ)/168755200)/ClassicalSixthBranch.v ((496012171:ℝ)/168755200) = (603683326587:ℝ)/289973000344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2720
  · change lowerPayment 2721 ≤ lowerValue ((point 2 split 4096 2721+point 2 split 4096 2722)/2)
    have hp : lowerPayment 2721 = (296716863180:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2721+point 2 split 4096 2722)/2 = (496070433:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496070433:ℝ)/168755200)/ClassicalSixthBranch.v ((496070433:ℝ)/168755200) = (603606012913:ℝ)/289924992456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2721
  · change lowerPayment 2722 ≤ lowerValue ((point 2 split 4096 2722+point 2 split 4096 2723)/2)
    have hp : lowerPayment 2722 = (296804634602:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2722+point 2 split 4096 2723)/2 = (99225739:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99225739:ℝ)/33751040)/ClassicalSixthBranch.v ((99225739:ℝ)/33751040) = (603528699239:ℝ)/289876984568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2722
  · change lowerPayment 2723 ≤ lowerValue ((point 2 split 4096 2723+point 2 split 4096 2724)/2)
    have hp : lowerPayment 2723 = (296892406753:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2723+point 2 split 4096 2724)/2 = (496186957:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496186957:ℝ)/168755200)/ClassicalSixthBranch.v ((496186957:ℝ)/168755200) = (120690277113:ℝ)/57965795336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2723
  · change lowerPayment 2724 ≤ lowerValue ((point 2 split 4096 2724+point 2 split 4096 2725)/2)
    have hp : lowerPayment 2724 = (296980179647:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2724+point 2 split 4096 2725)/2 = (496245219:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496245219:ℝ)/168755200)/ClassicalSixthBranch.v ((496245219:ℝ)/168755200) = (603374071891:ℝ)/289780968792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2724
  · change lowerPayment 2725 ≤ lowerValue ((point 2 split 4096 2725+point 2 split 4096 2726)/2)
    have hp : lowerPayment 2725 = (297067953297:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2725+point 2 split 4096 2726)/2 = (496303481:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496303481:ℝ)/168755200)/ClassicalSixthBranch.v ((496303481:ℝ)/168755200) = (603296758217:ℝ)/289732960904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2725
  · change lowerPayment 2726 ≤ lowerValue ((point 2 split 4096 2726+point 2 split 4096 2727)/2)
    have hp : lowerPayment 2726 = (297155727718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2726+point 2 split 4096 2727)/2 = (496361743:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496361743:ℝ)/168755200)/ClassicalSixthBranch.v ((496361743:ℝ)/168755200) = (603219444543:ℝ)/289684953016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2726
  · change lowerPayment 2727 ≤ lowerValue ((point 2 split 4096 2727+point 2 split 4096 2728)/2)
    have hp : lowerPayment 2727 = (297243502924:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2727+point 2 split 4096 2728)/2 = (99284001:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99284001:ℝ)/33751040)/ClassicalSixthBranch.v ((99284001:ℝ)/33751040) = (603142130869:ℝ)/289636945128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2727
  · change lowerPayment 2728 ≤ lowerValue ((point 2 split 4096 2728+point 2 split 4096 2729)/2)
    have hp : lowerPayment 2728 = (297331278930:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2728+point 2 split 4096 2729)/2 = (496478267:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496478267:ℝ)/168755200)/ClassicalSixthBranch.v ((496478267:ℝ)/168755200) = (120612963439:ℝ)/57917787448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2728
  · change lowerPayment 2729 ≤ lowerValue ((point 2 split 4096 2729+point 2 split 4096 2730)/2)
    have hp : lowerPayment 2729 = (297419055748:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2729+point 2 split 4096 2730)/2 = (4820743:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4820743:ℝ)/1638400)/ClassicalSixthBranch.v ((4820743:ℝ)/1638400) = (5854247607:ℝ)/2811076984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2729
  · change lowerPayment 2730 ≤ lowerValue ((point 2 split 4096 2730+point 2 split 4096 2731)/2)
    have hp : lowerPayment 2730 = (297506833394:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2730+point 2 split 4096 2731)/2 = (496594791:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496594791:ℝ)/168755200)/ClassicalSixthBranch.v ((496594791:ℝ)/168755200) = (602910189847:ℝ)/289492921464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2730
  · change lowerPayment 2731 ≤ lowerValue ((point 2 split 4096 2731+point 2 split 4096 2732)/2)
    have hp : lowerPayment 2731 = (297594611882:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2731+point 2 split 4096 2732)/2 = (496653053:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496653053:ℝ)/168755200)/ClassicalSixthBranch.v ((496653053:ℝ)/168755200) = (602832876173:ℝ)/289444913576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2731
  · change lowerPayment 2732 ≤ lowerValue ((point 2 split 4096 2732+point 2 split 4096 2733)/2)
    have hp : lowerPayment 2732 = (297682391226:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2732+point 2 split 4096 2733)/2 = (99342263:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99342263:ℝ)/33751040)/ClassicalSixthBranch.v ((99342263:ℝ)/33751040) = (602755562499:ℝ)/289396905688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2732
  · change lowerPayment 2733 ≤ lowerValue ((point 2 split 4096 2733+point 2 split 4096 2734)/2)
    have hp : lowerPayment 2733 = (297770171439:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2733+point 2 split 4096 2734)/2 = (496769577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496769577:ℝ)/168755200)/ClassicalSixthBranch.v ((496769577:ℝ)/168755200) = (24107129953:ℝ)/11573955912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2733
  · change lowerPayment 2734 ≤ lowerValue ((point 2 split 4096 2734+point 2 split 4096 2735)/2)
    have hp : lowerPayment 2734 = (297857952537:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2734+point 2 split 4096 2735)/2 = (496827839:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496827839:ℝ)/168755200)/ClassicalSixthBranch.v ((496827839:ℝ)/168755200) = (602600935151:ℝ)/289300889912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2734
  · change lowerPayment 2735 ≤ lowerValue ((point 2 split 4096 2735+point 2 split 4096 2736)/2)
    have hp : lowerPayment 2735 = (297945734533:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2735+point 2 split 4096 2736)/2 = (496886101:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496886101:ℝ)/168755200)/ClassicalSixthBranch.v ((496886101:ℝ)/168755200) = (602523621477:ℝ)/289252882024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2735
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_170
