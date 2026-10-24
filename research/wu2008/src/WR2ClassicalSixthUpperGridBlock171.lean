import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints171
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_171 (j : Fin 16) : upperPayment (16*171+j.val) ≤
    upperValue ((point split endpoint 4096 (16*171+j.val)+point split endpoint 4096 (16*171+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2736 ≤ upperValue ((point split endpoint 4096 2736+point split endpoint 4096 2737)/2)
    have hp : upperPayment 2736 = (193988242276:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2736+point split endpoint 4096 2737)/2 = (644974527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644974527:ℝ)/168755200)*ClassicalSixthBranch.v ((644974527:ℝ)/168755200)/ClassicalSixthBranch.r = (99350011848465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2736
  · change upperPayment 2737 ≤ upperValue ((point split endpoint 4096 2737+point split endpoint 4096 2738)/2)
    have hp : upperPayment 2737 = (193868847906:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2737+point split endpoint 4096 2738)/2 = (644999677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644999677:ℝ)/168755200)*ClassicalSixthBranch.v ((644999677:ℝ)/168755200)/ClassicalSixthBranch.r = (99329534416665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2737
  · change upperPayment 2738 ≤ upperValue ((point split endpoint 4096 2738+point split endpoint 4096 2739)/2)
    have hp : upperPayment 2738 = (193749422877:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2738+point split endpoint 4096 2739)/2 = (645024827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645024827:ℝ)/168755200)*ClassicalSixthBranch.v ((645024827:ℝ)/168755200)/ClassicalSixthBranch.r = (99309059008937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2738
  · change upperPayment 2739 ≤ upperValue ((point split endpoint 4096 2739+point split endpoint 4096 2740)/2)
    have hp : upperPayment 2739 = (193629967181:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2739+point split endpoint 4096 2740)/2 = (645049977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645049977:ℝ)/168755200)*ClassicalSixthBranch.v ((645049977:ℝ)/168755200)/ClassicalSixthBranch.r = (99288585625281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2739
  · change upperPayment 2740 ≤ upperValue ((point split endpoint 4096 2740+point split endpoint 4096 2741)/2)
    have hp : upperPayment 2740 = (193510480810:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2740+point split endpoint 4096 2741)/2 = (645075127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645075127:ℝ)/168755200)*ClassicalSixthBranch.v ((645075127:ℝ)/168755200)/ClassicalSixthBranch.r = (99268114265697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2740
  · change upperPayment 2741 ≤ upperValue ((point split endpoint 4096 2741+point split endpoint 4096 2742)/2)
    have hp : upperPayment 2741 = (193390963759:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2741+point split endpoint 4096 2742)/2 = (645100277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645100277:ℝ)/168755200)*ClassicalSixthBranch.v ((645100277:ℝ)/168755200)/ClassicalSixthBranch.r = (99247644930185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2741
  · change upperPayment 2742 ≤ upperValue ((point split endpoint 4096 2742+point split endpoint 4096 2743)/2)
    have hp : upperPayment 2742 = (193271416019:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2742+point split endpoint 4096 2743)/2 = (645125427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645125427:ℝ)/168755200)*ClassicalSixthBranch.v ((645125427:ℝ)/168755200)/ClassicalSixthBranch.r = (99227177618745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2742
  · change upperPayment 2743 ≤ upperValue ((point split endpoint 4096 2743+point split endpoint 4096 2744)/2)
    have hp : upperPayment 2743 = (193151837584:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2743+point split endpoint 4096 2744)/2 = (645150577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645150577:ℝ)/168755200)*ClassicalSixthBranch.v ((645150577:ℝ)/168755200)/ClassicalSixthBranch.r = (99206712331377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2743
  · change upperPayment 2744 ≤ upperValue ((point split endpoint 4096 2744+point split endpoint 4096 2745)/2)
    have hp : upperPayment 2744 = (193032228448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2744+point split endpoint 4096 2745)/2 = (645175727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645175727:ℝ)/168755200)*ClassicalSixthBranch.v ((645175727:ℝ)/168755200)/ClassicalSixthBranch.r = (99186249068081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2744
  · change upperPayment 2745 ≤ upperValue ((point split endpoint 4096 2745+point split endpoint 4096 2746)/2)
    have hp : upperPayment 2745 = (192912588602:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2745+point split endpoint 4096 2746)/2 = (645200877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645200877:ℝ)/168755200)*ClassicalSixthBranch.v ((645200877:ℝ)/168755200)/ClassicalSixthBranch.r = (99165787828857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2745
  · change upperPayment 2746 ≤ upperValue ((point split endpoint 4096 2746+point split endpoint 4096 2747)/2)
    have hp : upperPayment 2746 = (192792918041:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2746+point split endpoint 4096 2747)/2 = (645226027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645226027:ℝ)/168755200)*ClassicalSixthBranch.v ((645226027:ℝ)/168755200)/ClassicalSixthBranch.r = (99145328613705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2746
  · change upperPayment 2747 ≤ upperValue ((point split endpoint 4096 2747+point split endpoint 4096 2748)/2)
    have hp : upperPayment 2747 = (192673216757:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2747+point split endpoint 4096 2748)/2 = (645251177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645251177:ℝ)/168755200)*ClassicalSixthBranch.v ((645251177:ℝ)/168755200)/ClassicalSixthBranch.r = (99124871422625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2747
  · change upperPayment 2748 ≤ upperValue ((point split endpoint 4096 2748+point split endpoint 4096 2749)/2)
    have hp : upperPayment 2748 = (192553484743:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2748+point split endpoint 4096 2749)/2 = (645276327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645276327:ℝ)/168755200)*ClassicalSixthBranch.v ((645276327:ℝ)/168755200)/ClassicalSixthBranch.r = (99104416255617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2748
  · change upperPayment 2749 ≤ upperValue ((point split endpoint 4096 2749+point split endpoint 4096 2750)/2)
    have hp : upperPayment 2749 = (192433721992:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2749+point split endpoint 4096 2750)/2 = (645301477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645301477:ℝ)/168755200)*ClassicalSixthBranch.v ((645301477:ℝ)/168755200)/ClassicalSixthBranch.r = (99083963112681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2749
  · change upperPayment 2750 ≤ upperValue ((point split endpoint 4096 2750+point split endpoint 4096 2751)/2)
    have hp : upperPayment 2750 = (192313928497:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2750+point split endpoint 4096 2751)/2 = (645326627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645326627:ℝ)/168755200)*ClassicalSixthBranch.v ((645326627:ℝ)/168755200)/ClassicalSixthBranch.r = (99063511993817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2750
  · change upperPayment 2751 ≤ upperValue ((point split endpoint 4096 2751+point split endpoint 4096 2752)/2)
    have hp : upperPayment 2751 = (192194104251:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2751+point split endpoint 4096 2752)/2 = (645351777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645351777:ℝ)/168755200)*ClassicalSixthBranch.v ((645351777:ℝ)/168755200)/ClassicalSixthBranch.r = (99043062899025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2751
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_171
