import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints230
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_230 (j : Fin 16) : lowerPayment (16*230+j.val) ≤
    lowerValue ((point 2 split 4096 (16*230+j.val)+point 2 split 4096 (16*230+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3680 ≤ lowerValue ((point 2 split 4096 3680+point 2 split 4096 3681)/2)
    have hp : lowerPayment 3680 = (383313252254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3680+point 2 split 4096 3681)/2 = (551943691:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551943691:ℝ)/168755200)/ClassicalSixthBranch.v ((551943691:ℝ)/168755200) = (529462199547:ℝ)/243885427864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3680
  · change lowerPayment 3681 ≤ lowerValue ((point 2 split 4096 3681+point 2 split 4096 3682)/2)
    have hp : lowerPayment 3681 = (383408332706:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3681+point 2 split 4096 3682)/2 = (552001953:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552001953:ℝ)/168755200)/ClassicalSixthBranch.v ((552001953:ℝ)/168755200) = (529384885873:ℝ)/243837419976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3681
  · change lowerPayment 3682 ≤ lowerValue ((point 2 split 4096 3682+point 2 split 4096 3683)/2)
    have hp : lowerPayment 3682 = (383503428051:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3682+point 2 split 4096 3683)/2 = (110412043:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110412043:ℝ)/33751040)/ClassicalSixthBranch.v ((110412043:ℝ)/33751040) = (529307572199:ℝ)/243789412088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3682
  · change lowerPayment 3683 ≤ lowerValue ((point 2 split 4096 3683+point 2 split 4096 3684)/2)
    have hp : lowerPayment 3683 = (383598538304:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3683+point 2 split 4096 3684)/2 = (552118477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552118477:ℝ)/168755200)/ClassicalSixthBranch.v ((552118477:ℝ)/168755200) = (21169210341:ℝ)/9749656168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3683
  · change lowerPayment 3684 ≤ lowerValue ((point 2 split 4096 3684+point 2 split 4096 3685)/2)
    have hp : lowerPayment 3684 = (383693663483:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3684+point 2 split 4096 3685)/2 = (552176739:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552176739:ℝ)/168755200)/ClassicalSixthBranch.v ((552176739:ℝ)/168755200) = (529152944851:ℝ)/243693396312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3684
  · change lowerPayment 3685 ≤ lowerValue ((point 2 split 4096 3685+point 2 split 4096 3686)/2)
    have hp : lowerPayment 3685 = (383788803604:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3685+point 2 split 4096 3686)/2 = (552235001:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552235001:ℝ)/168755200)/ClassicalSixthBranch.v ((552235001:ℝ)/168755200) = (529075631177:ℝ)/243645388424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3685
  · change lowerPayment 3686 ≤ lowerValue ((point 2 split 4096 3686+point 2 split 4096 3687)/2)
    have hp : lowerPayment 3686 = (383883958684:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3686+point 2 split 4096 3687)/2 = (552293263:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552293263:ℝ)/168755200)/ClassicalSixthBranch.v ((552293263:ℝ)/168755200) = (528998317503:ℝ)/243597380536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3686
  · change lowerPayment 3687 ≤ lowerValue ((point 2 split 4096 3687+point 2 split 4096 3688)/2)
    have hp : lowerPayment 3687 = (383979128738:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3687+point 2 split 4096 3688)/2 = (22094061:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22094061:ℝ)/6750208)/ClassicalSixthBranch.v ((22094061:ℝ)/6750208) = (528921003829:ℝ)/243549372648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3687
  · change lowerPayment 3688 ≤ lowerValue ((point 2 split 4096 3688+point 2 split 4096 3689)/2)
    have hp : lowerPayment 3688 = (384074313784:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3688+point 2 split 4096 3689)/2 = (552409787:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552409787:ℝ)/168755200)/ClassicalSixthBranch.v ((552409787:ℝ)/168755200) = (105768738031:ℝ)/48700272952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3688
  · change lowerPayment 3689 ≤ lowerValue ((point 2 split 4096 3689+point 2 split 4096 3690)/2)
    have hp : lowerPayment 3689 = (384169513838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3689+point 2 split 4096 3690)/2 = (552468049:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552468049:ℝ)/168755200)/ClassicalSixthBranch.v ((552468049:ℝ)/168755200) = (528766376481:ℝ)/243453356872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3689
  · change lowerPayment 3690 ≤ lowerValue ((point 2 split 4096 3690+point 2 split 4096 3691)/2)
    have hp : lowerPayment 3690 = (384264728916:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3690+point 2 split 4096 3691)/2 = (552526311:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552526311:ℝ)/168755200)/ClassicalSixthBranch.v ((552526311:ℝ)/168755200) = (528689062807:ℝ)/243405348984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3690
  · change lowerPayment 3691 ≤ lowerValue ((point 2 split 4096 3691+point 2 split 4096 3692)/2)
    have hp : lowerPayment 3691 = (384359959035:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3691+point 2 split 4096 3692)/2 = (552584573:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552584573:ℝ)/168755200)/ClassicalSixthBranch.v ((552584573:ℝ)/168755200) = (528611749133:ℝ)/243357341096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3691
  · change lowerPayment 3692 ≤ lowerValue ((point 2 split 4096 3692+point 2 split 4096 3693)/2)
    have hp : lowerPayment 3692 = (384455204212:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3692+point 2 split 4096 3693)/2 = (110528567:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110528567:ℝ)/33751040)/ClassicalSixthBranch.v ((110528567:ℝ)/33751040) = (528534435459:ℝ)/243309333208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3692
  · change lowerPayment 3693 ≤ lowerValue ((point 2 split 4096 3693+point 2 split 4096 3694)/2)
    have hp : lowerPayment 3693 = (384550464463:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3693+point 2 split 4096 3694)/2 = (552701097:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552701097:ℝ)/168755200)/ClassicalSixthBranch.v ((552701097:ℝ)/168755200) = (105691424357:ℝ)/48652265064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3693
  · change lowerPayment 3694 ≤ lowerValue ((point 2 split 4096 3694+point 2 split 4096 3695)/2)
    have hp : lowerPayment 3694 = (384645739804:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3694+point 2 split 4096 3695)/2 = (552759359:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552759359:ℝ)/168755200)/ClassicalSixthBranch.v ((552759359:ℝ)/168755200) = (528379808111:ℝ)/243213317432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3694
  · change lowerPayment 3695 ≤ lowerValue ((point 2 split 4096 3695+point 2 split 4096 3696)/2)
    have hp : lowerPayment 3695 = (384741030253:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3695+point 2 split 4096 3696)/2 = (552817621:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552817621:ℝ)/168755200)/ClassicalSixthBranch.v ((552817621:ℝ)/168755200) = (528302494437:ℝ)/243165309544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3695
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_230
