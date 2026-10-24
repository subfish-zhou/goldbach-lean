import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints171
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_171 (j : Fin 16) : lowerPayment (16*171+j.val) ≤
    lowerValue ((point 2 split 4096 (16*171+j.val)+point 2 split 4096 (16*171+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2736 ≤ lowerValue ((point 2 split 4096 2736+point 2 split 4096 2737)/2)
    have hp : lowerPayment 2736 = (298033517442:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2736+point 2 split 4096 2737)/2 = (496944363:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((496944363:ℝ)/168755200)/ClassicalSixthBranch.v ((496944363:ℝ)/168755200) = (602446307803:ℝ)/289204874136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2736
  · change lowerPayment 2737 ≤ lowerValue ((point 2 split 4096 2737+point 2 split 4096 2738)/2)
    have hp : lowerPayment 2737 = (298121301277:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2737+point 2 split 4096 2738)/2 = (19880105:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19880105:ℝ)/6750208)/ClassicalSixthBranch.v ((19880105:ℝ)/6750208) = (602368994129:ℝ)/289156866248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2737
  · change lowerPayment 2738 ≤ lowerValue ((point 2 split 4096 2738+point 2 split 4096 2739)/2)
    have hp : lowerPayment 2738 = (298209086053:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2738+point 2 split 4096 2739)/2 = (497060887:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497060887:ℝ)/168755200)/ClassicalSixthBranch.v ((497060887:ℝ)/168755200) = (120458336091:ℝ)/57821771672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2738
  · change lowerPayment 2739 ≤ lowerValue ((point 2 split 4096 2739+point 2 split 4096 2740)/2)
    have hp : lowerPayment 2739 = (298296871783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2739+point 2 split 4096 2740)/2 = (497119149:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497119149:ℝ)/168755200)/ClassicalSixthBranch.v ((497119149:ℝ)/168755200) = (602214366781:ℝ)/289060850472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2739
  · change lowerPayment 2740 ≤ lowerValue ((point 2 split 4096 2740+point 2 split 4096 2741)/2)
    have hp : lowerPayment 2740 = (298384658483:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2740+point 2 split 4096 2741)/2 = (497177411:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497177411:ℝ)/168755200)/ClassicalSixthBranch.v ((497177411:ℝ)/168755200) = (602137053107:ℝ)/289012842584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2740
  · change lowerPayment 2741 ≤ lowerValue ((point 2 split 4096 2741+point 2 split 4096 2742)/2)
    have hp : lowerPayment 2741 = (298472446166:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2741+point 2 split 4096 2742)/2 = (497235673:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497235673:ℝ)/168755200)/ClassicalSixthBranch.v ((497235673:ℝ)/168755200) = (602059739433:ℝ)/288964834696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2741
  · change lowerPayment 2742 ≤ lowerValue ((point 2 split 4096 2742+point 2 split 4096 2743)/2)
    have hp : lowerPayment 2742 = (298560234847:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2742+point 2 split 4096 2743)/2 = (99458787:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99458787:ℝ)/33751040)/ClassicalSixthBranch.v ((99458787:ℝ)/33751040) = (601982425759:ℝ)/288916826808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2742
  · change lowerPayment 2743 ≤ lowerValue ((point 2 split 4096 2743+point 2 split 4096 2744)/2)
    have hp : lowerPayment 2743 = (298648024538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2743+point 2 split 4096 2744)/2 = (497352197:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497352197:ℝ)/168755200)/ClassicalSixthBranch.v ((497352197:ℝ)/168755200) = (120381022417:ℝ)/57773763784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2743
  · change lowerPayment 2744 ≤ lowerValue ((point 2 split 4096 2744+point 2 split 4096 2745)/2)
    have hp : lowerPayment 2744 = (298735815256:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2744+point 2 split 4096 2745)/2 = (497410459:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497410459:ℝ)/168755200)/ClassicalSixthBranch.v ((497410459:ℝ)/168755200) = (601827798411:ℝ)/288820811032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2744
  · change lowerPayment 2745 ≤ lowerValue ((point 2 split 4096 2745+point 2 split 4096 2746)/2)
    have hp : lowerPayment 2745 = (298823607014:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2745+point 2 split 4096 2746)/2 = (497468721:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497468721:ℝ)/168755200)/ClassicalSixthBranch.v ((497468721:ℝ)/168755200) = (601750484737:ℝ)/288772803144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2745
  · change lowerPayment 2746 ≤ lowerValue ((point 2 split 4096 2746+point 2 split 4096 2747)/2)
    have hp : lowerPayment 2746 = (298911399825:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2746+point 2 split 4096 2747)/2 = (497526983:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497526983:ℝ)/168755200)/ClassicalSixthBranch.v ((497526983:ℝ)/168755200) = (601673171063:ℝ)/288724795256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2746
  · change lowerPayment 2747 ≤ lowerValue ((point 2 split 4096 2747+point 2 split 4096 2748)/2)
    have hp : lowerPayment 2747 = (298999193704:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2747+point 2 split 4096 2748)/2 = (99517049:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99517049:ℝ)/33751040)/ClassicalSixthBranch.v ((99517049:ℝ)/33751040) = (601595857389:ℝ)/288676787368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2747
  · change lowerPayment 2748 ≤ lowerValue ((point 2 split 4096 2748+point 2 split 4096 2749)/2)
    have hp : lowerPayment 2748 = (299086988666:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2748+point 2 split 4096 2749)/2 = (497643507:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497643507:ℝ)/168755200)/ClassicalSixthBranch.v ((497643507:ℝ)/168755200) = (120303708743:ℝ)/57725755896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2748
  · change lowerPayment 2749 ≤ lowerValue ((point 2 split 4096 2749+point 2 split 4096 2750)/2)
    have hp : lowerPayment 2749 = (299174784724:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2749+point 2 split 4096 2750)/2 = (497701769:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497701769:ℝ)/168755200)/ClassicalSixthBranch.v ((497701769:ℝ)/168755200) = (601441230041:ℝ)/288580771592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2749
  · change lowerPayment 2750 ≤ lowerValue ((point 2 split 4096 2750+point 2 split 4096 2751)/2)
    have hp : lowerPayment 2750 = (299262581893:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2750+point 2 split 4096 2751)/2 = (497760031:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497760031:ℝ)/168755200)/ClassicalSixthBranch.v ((497760031:ℝ)/168755200) = (601363916367:ℝ)/288532763704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2750
  · change lowerPayment 2751 ≤ lowerValue ((point 2 split 4096 2751+point 2 split 4096 2752)/2)
    have hp : lowerPayment 2751 = (299350380186:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2751+point 2 split 4096 2752)/2 = (497818293:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((497818293:ℝ)/168755200)/ClassicalSixthBranch.v ((497818293:ℝ)/168755200) = (601286602693:ℝ)/288484755816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2751
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_171
