import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints164
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_164 (j : Fin 16) : upperPayment (16*164+j.val) ≤
    upperValue ((point split endpoint 4096 (16*164+j.val)+point split endpoint 4096 (16*164+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2624 ≤ upperValue ((point split endpoint 4096 2624+point split endpoint 4096 2625)/2)
    have hp : upperPayment 2624 = (207168048858:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2624+point split endpoint 4096 2625)/2 = (642157727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642157727:ℝ)/168755200)*ClassicalSixthBranch.v ((642157727:ℝ)/168755200)/ClassicalSixthBranch.r = (101656292537681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2624
  · change upperPayment 2625 ≤ upperValue ((point split endpoint 4096 2625+point split endpoint 4096 2626)/2)
    have hp : upperPayment 2625 = (207052045043:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2625+point split endpoint 4096 2626)/2 = (642182877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642182877:ℝ)/168755200)*ClassicalSixthBranch.v ((642182877:ℝ)/168755200)/ClassicalSixthBranch.r = (101635588409817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2625
  · change upperPayment 2626 ≤ upperValue ((point split endpoint 4096 2626+point split endpoint 4096 2627)/2)
    have hp : upperPayment 2626 = (206936011330:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2626+point split endpoint 4096 2627)/2 = (642208027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642208027:ℝ)/168755200)*ClassicalSixthBranch.v ((642208027:ℝ)/168755200)/ClassicalSixthBranch.r = (101614886306025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2626
  · change upperPayment 2627 ≤ upperValue ((point split endpoint 4096 2627+point split endpoint 4096 2628)/2)
    have hp : upperPayment 2627 = (206819947713:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2627+point split endpoint 4096 2628)/2 = (642233177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642233177:ℝ)/168755200)*ClassicalSixthBranch.v ((642233177:ℝ)/168755200)/ClassicalSixthBranch.r = (101594186226305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2627
  · change upperPayment 2628 ≤ upperValue ((point split endpoint 4096 2628+point split endpoint 4096 2629)/2)
    have hp : upperPayment 2628 = (206703854184:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2628+point split endpoint 4096 2629)/2 = (642258327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642258327:ℝ)/168755200)*ClassicalSixthBranch.v ((642258327:ℝ)/168755200)/ClassicalSixthBranch.r = (101573488170657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2628
  · change upperPayment 2629 ≤ upperValue ((point split endpoint 4096 2629+point split endpoint 4096 2630)/2)
    have hp : upperPayment 2629 = (206587730737:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2629+point split endpoint 4096 2630)/2 = (642283477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642283477:ℝ)/168755200)*ClassicalSixthBranch.v ((642283477:ℝ)/168755200)/ClassicalSixthBranch.r = (101552792139081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2629
  · change upperPayment 2630 ≤ upperValue ((point split endpoint 4096 2630+point split endpoint 4096 2631)/2)
    have hp : upperPayment 2630 = (206471577366:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2630+point split endpoint 4096 2631)/2 = (642308627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642308627:ℝ)/168755200)*ClassicalSixthBranch.v ((642308627:ℝ)/168755200)/ClassicalSixthBranch.r = (101532098131577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2630
  · change upperPayment 2631 ≤ upperValue ((point split endpoint 4096 2631+point split endpoint 4096 2632)/2)
    have hp : upperPayment 2631 = (206355394063:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2631+point split endpoint 4096 2632)/2 = (642333777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642333777:ℝ)/168755200)*ClassicalSixthBranch.v ((642333777:ℝ)/168755200)/ClassicalSixthBranch.r = (101511406148145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2631
  · change upperPayment 2632 ≤ upperValue ((point split endpoint 4096 2632+point split endpoint 4096 2633)/2)
    have hp : upperPayment 2632 = (206239180822:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2632+point split endpoint 4096 2633)/2 = (642358927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642358927:ℝ)/168755200)*ClassicalSixthBranch.v ((642358927:ℝ)/168755200)/ClassicalSixthBranch.r = (101490716188785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2632
  · change upperPayment 2633 ≤ upperValue ((point split endpoint 4096 2633+point split endpoint 4096 2634)/2)
    have hp : upperPayment 2633 = (206122937637:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2633+point split endpoint 4096 2634)/2 = (642384077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642384077:ℝ)/168755200)*ClassicalSixthBranch.v ((642384077:ℝ)/168755200)/ClassicalSixthBranch.r = (101470028253497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2633
  · change upperPayment 2634 ≤ upperValue ((point split endpoint 4096 2634+point split endpoint 4096 2635)/2)
    have hp : upperPayment 2634 = (206006664500:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2634+point split endpoint 4096 2635)/2 = (642409227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642409227:ℝ)/168755200)*ClassicalSixthBranch.v ((642409227:ℝ)/168755200)/ClassicalSixthBranch.r = (101449342342281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2634
  · change upperPayment 2635 ≤ upperValue ((point split endpoint 4096 2635+point split endpoint 4096 2636)/2)
    have hp : upperPayment 2635 = (205890361406:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2635+point split endpoint 4096 2636)/2 = (642434377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642434377:ℝ)/168755200)*ClassicalSixthBranch.v ((642434377:ℝ)/168755200)/ClassicalSixthBranch.r = (101428658455137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2635
  · change upperPayment 2636 ≤ upperValue ((point split endpoint 4096 2636+point split endpoint 4096 2637)/2)
    have hp : upperPayment 2636 = (205774028346:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2636+point split endpoint 4096 2637)/2 = (642459527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642459527:ℝ)/168755200)*ClassicalSixthBranch.v ((642459527:ℝ)/168755200)/ClassicalSixthBranch.r = (101407976592065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2636
  · change upperPayment 2637 ≤ upperValue ((point split endpoint 4096 2637+point split endpoint 4096 2638)/2)
    have hp : upperPayment 2637 = (205657665316:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2637+point split endpoint 4096 2638)/2 = (642484677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642484677:ℝ)/168755200)*ClassicalSixthBranch.v ((642484677:ℝ)/168755200)/ClassicalSixthBranch.r = (101387296753065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2637
  · change upperPayment 2638 ≤ upperValue ((point split endpoint 4096 2638+point split endpoint 4096 2639)/2)
    have hp : upperPayment 2638 = (205541272307:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2638+point split endpoint 4096 2639)/2 = (642509827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642509827:ℝ)/168755200)*ClassicalSixthBranch.v ((642509827:ℝ)/168755200)/ClassicalSixthBranch.r = (101366618938137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2638
  · change upperPayment 2639 ≤ upperValue ((point split endpoint 4096 2639+point split endpoint 4096 2640)/2)
    have hp : upperPayment 2639 = (205424849314:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2639+point split endpoint 4096 2640)/2 = (642534977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642534977:ℝ)/168755200)*ClassicalSixthBranch.v ((642534977:ℝ)/168755200)/ClassicalSixthBranch.r = (101345943147281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2639
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_164
