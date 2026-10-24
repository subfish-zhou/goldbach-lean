import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints164
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_164 (j : Fin 16) : lowerPayment (16*164+j.val) ≤
    lowerValue ((point 2 split 4096 (16*164+j.val)+point 2 split 4096 (16*164+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2624 ≤ lowerValue ((point 2 split 4096 2624+point 2 split 4096 2625)/2)
    have hp : lowerPayment 2624 = (288204271065:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2624+point 2 split 4096 2625)/2 = (490419019:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490419019:ℝ)/168755200)/ClassicalSixthBranch.v ((490419019:ℝ)/168755200) = (611105439291:ℝ)/294581757592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2624
  · change lowerPayment 2625 ≤ lowerValue ((point 2 split 4096 2625+point 2 split 4096 2626)/2)
    have hp : lowerPayment 2625 = (288292039336:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2625+point 2 split 4096 2626)/2 = (490477281:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490477281:ℝ)/168755200)/ClassicalSixthBranch.v ((490477281:ℝ)/168755200) = (611028125617:ℝ)/294533749704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2625
  · change lowerPayment 2626 ≤ lowerValue ((point 2 split 4096 2626+point 2 split 4096 2627)/2)
    have hp : lowerPayment 2626 = (288379806956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2626+point 2 split 4096 2627)/2 = (4762481:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4762481:ℝ)/1638400)/ClassicalSixthBranch.v ((4762481:ℝ)/1638400) = (5931561281:ℝ)/2859084872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2626
  · change lowerPayment 2627 ≤ lowerValue ((point 2 split 4096 2627+point 2 split 4096 2628)/2)
    have hp : lowerPayment 2627 = (288467573940:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2627+point 2 split 4096 2628)/2 = (98118761:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98118761:ℝ)/33751040)/ClassicalSixthBranch.v ((98118761:ℝ)/33751040) = (610873498269:ℝ)/294437733928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2627
  · change lowerPayment 2628 ≤ lowerValue ((point 2 split 4096 2628+point 2 split 4096 2629)/2)
    have hp : lowerPayment 2628 = (288555340301:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2628+point 2 split 4096 2629)/2 = (490652067:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490652067:ℝ)/168755200)/ClassicalSixthBranch.v ((490652067:ℝ)/168755200) = (122159236919:ℝ)/58877945208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2628
  · change lowerPayment 2629 ≤ lowerValue ((point 2 split 4096 2629+point 2 split 4096 2630)/2)
    have hp : lowerPayment 2629 = (288643106053:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2629+point 2 split 4096 2630)/2 = (490710329:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490710329:ℝ)/168755200)/ClassicalSixthBranch.v ((490710329:ℝ)/168755200) = (610718870921:ℝ)/294341718152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2629
  · change lowerPayment 2630 ≤ lowerValue ((point 2 split 4096 2630+point 2 split 4096 2631)/2)
    have hp : lowerPayment 2630 = (288730871212:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2630+point 2 split 4096 2631)/2 = (490768591:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490768591:ℝ)/168755200)/ClassicalSixthBranch.v ((490768591:ℝ)/168755200) = (610641557247:ℝ)/294293710264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2630
  · change lowerPayment 2631 ≤ lowerValue ((point 2 split 4096 2631+point 2 split 4096 2632)/2)
    have hp : lowerPayment 2631 = (288818635791:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2631+point 2 split 4096 2632)/2 = (490826853:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490826853:ℝ)/168755200)/ClassicalSixthBranch.v ((490826853:ℝ)/168755200) = (610564243573:ℝ)/294245702376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2631
  · change lowerPayment 2632 ≤ lowerValue ((point 2 split 4096 2632+point 2 split 4096 2633)/2)
    have hp : lowerPayment 2632 = (288906399804:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2632+point 2 split 4096 2633)/2 = (98177023:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98177023:ℝ)/33751040)/ClassicalSixthBranch.v ((98177023:ℝ)/33751040) = (610486929899:ℝ)/294197694488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2632
  · change lowerPayment 2633 ≤ lowerValue ((point 2 split 4096 2633+point 2 split 4096 2634)/2)
    have hp : lowerPayment 2633 = (288994163267:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2633+point 2 split 4096 2634)/2 = (490943377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490943377:ℝ)/168755200)/ClassicalSixthBranch.v ((490943377:ℝ)/168755200) = (24416384649:ℝ)/11765987464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2633
  · change lowerPayment 2634 ≤ lowerValue ((point 2 split 4096 2634+point 2 split 4096 2635)/2)
    have hp : lowerPayment 2634 = (289081926192:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2634+point 2 split 4096 2635)/2 = (491001639:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491001639:ℝ)/168755200)/ClassicalSixthBranch.v ((491001639:ℝ)/168755200) = (610332302551:ℝ)/294101678712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2634
  · change lowerPayment 2635 ≤ lowerValue ((point 2 split 4096 2635+point 2 split 4096 2636)/2)
    have hp : lowerPayment 2635 = (289169688595:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2635+point 2 split 4096 2636)/2 = (491059901:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491059901:ℝ)/168755200)/ClassicalSixthBranch.v ((491059901:ℝ)/168755200) = (610254988877:ℝ)/294053670824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2635
  · change lowerPayment 2636 ≤ lowerValue ((point 2 split 4096 2636+point 2 split 4096 2637)/2)
    have hp : lowerPayment 2636 = (289257450490:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2636+point 2 split 4096 2637)/2 = (491118163:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491118163:ℝ)/168755200)/ClassicalSixthBranch.v ((491118163:ℝ)/168755200) = (610177675203:ℝ)/294005662936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2636
  · change lowerPayment 2637 ≤ lowerValue ((point 2 split 4096 2637+point 2 split 4096 2638)/2)
    have hp : lowerPayment 2637 = (289345211890:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2637+point 2 split 4096 2638)/2 = (19647057:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19647057:ℝ)/6750208)/ClassicalSixthBranch.v ((19647057:ℝ)/6750208) = (610100361529:ℝ)/293957655048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2637
  · change lowerPayment 2638 ≤ lowerValue ((point 2 split 4096 2638+point 2 split 4096 2639)/2)
    have hp : lowerPayment 2638 = (289432972811:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2638+point 2 split 4096 2639)/2 = (491234687:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491234687:ℝ)/168755200)/ClassicalSixthBranch.v ((491234687:ℝ)/168755200) = (122004609571:ℝ)/58781929432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2638
  · change lowerPayment 2639 ≤ lowerValue ((point 2 split 4096 2639+point 2 split 4096 2640)/2)
    have hp : lowerPayment 2639 = (289520733267:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2639+point 2 split 4096 2640)/2 = (491292949:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491292949:ℝ)/168755200)/ClassicalSixthBranch.v ((491292949:ℝ)/168755200) = (609945734181:ℝ)/293861639272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2639
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_164
