import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints162
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_162 (j : Fin 16) : upperPayment (16*162+j.val) ≤
    upperValue ((point split endpoint 4096 (16*162+j.val)+point split endpoint 4096 (16*162+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2592 ≤ upperValue ((point split endpoint 4096 2592+point split endpoint 4096 2593)/2)
    have hp : upperPayment 2592 = (210864424472:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2592+point split endpoint 4096 2593)/2 = (641352927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641352927:ℝ)/168755200)*ClassicalSixthBranch.v ((641352927:ℝ)/168755200)/ClassicalSixthBranch.r = (102319893339345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2592
  · change upperPayment 2593 ≤ upperValue ((point split endpoint 4096 2593+point split endpoint 4096 2594)/2)
    have hp : upperPayment 2593 = (210749373895:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2593+point split endpoint 4096 2594)/2 = (641378077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641378077:ℝ)/168755200)*ClassicalSixthBranch.v ((641378077:ℝ)/168755200)/ClassicalSixthBranch.r = (102299124441177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2593
  · change upperPayment 2594 ≤ upperValue ((point split endpoint 4096 2594+point split endpoint 4096 2595)/2)
    have hp : upperPayment 2594 = (210634293632:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2594+point split endpoint 4096 2595)/2 = (641403227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641403227:ℝ)/168755200)*ClassicalSixthBranch.v ((641403227:ℝ)/168755200)/ClassicalSixthBranch.r = (102278357567081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2594
  · change upperPayment 2595 ≤ upperValue ((point split endpoint 4096 2595+point split endpoint 4096 2596)/2)
    have hp : upperPayment 2595 = (210519183676:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2595+point split endpoint 4096 2596)/2 = (641428377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641428377:ℝ)/168755200)*ClassicalSixthBranch.v ((641428377:ℝ)/168755200)/ClassicalSixthBranch.r = (102257592717057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2595
  · change upperPayment 2596 ≤ upperValue ((point split endpoint 4096 2596+point split endpoint 4096 2597)/2)
    have hp : upperPayment 2596 = (210404044021:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2596+point split endpoint 4096 2597)/2 = (641453527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641453527:ℝ)/168755200)*ClassicalSixthBranch.v ((641453527:ℝ)/168755200)/ClassicalSixthBranch.r = (102236829891105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2596
  · change upperPayment 2597 ≤ upperValue ((point split endpoint 4096 2597+point split endpoint 4096 2598)/2)
    have hp : upperPayment 2597 = (210288874659:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2597+point split endpoint 4096 2598)/2 = (641478677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641478677:ℝ)/168755200)*ClassicalSixthBranch.v ((641478677:ℝ)/168755200)/ClassicalSixthBranch.r = (102216069089225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2597
  · change upperPayment 2598 ≤ upperValue ((point split endpoint 4096 2598+point split endpoint 4096 2599)/2)
    have hp : upperPayment 2598 = (210173675584:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2598+point split endpoint 4096 2599)/2 = (641503827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641503827:ℝ)/168755200)*ClassicalSixthBranch.v ((641503827:ℝ)/168755200)/ClassicalSixthBranch.r = (102195310311417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2598
  · change upperPayment 2599 ≤ upperValue ((point split endpoint 4096 2599+point split endpoint 4096 2600)/2)
    have hp : upperPayment 2599 = (210058446790:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2599+point split endpoint 4096 2600)/2 = (641528977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641528977:ℝ)/168755200)*ClassicalSixthBranch.v ((641528977:ℝ)/168755200)/ClassicalSixthBranch.r = (102174553557681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2599
  · change upperPayment 2600 ≤ upperValue ((point split endpoint 4096 2600+point split endpoint 4096 2601)/2)
    have hp : upperPayment 2600 = (209943188271:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2600+point split endpoint 4096 2601)/2 = (641554127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641554127:ℝ)/168755200)*ClassicalSixthBranch.v ((641554127:ℝ)/168755200)/ClassicalSixthBranch.r = (102153798828017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2600
  · change upperPayment 2601 ≤ upperValue ((point split endpoint 4096 2601+point split endpoint 4096 2602)/2)
    have hp : upperPayment 2601 = (209827900018:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2601+point split endpoint 4096 2602)/2 = (641579277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641579277:ℝ)/168755200)*ClassicalSixthBranch.v ((641579277:ℝ)/168755200)/ClassicalSixthBranch.r = (102133046122425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2601
  · change upperPayment 2602 ≤ upperValue ((point split endpoint 4096 2602+point split endpoint 4096 2603)/2)
    have hp : upperPayment 2602 = (209712582027:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2602+point split endpoint 4096 2603)/2 = (641604427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641604427:ℝ)/168755200)*ClassicalSixthBranch.v ((641604427:ℝ)/168755200)/ClassicalSixthBranch.r = (991381509135:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2602
  · change upperPayment 2603 ≤ upperValue ((point split endpoint 4096 2603+point split endpoint 4096 2604)/2)
    have hp : upperPayment 2603 = (209597234290:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2603+point split endpoint 4096 2604)/2 = (641629577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641629577:ℝ)/168755200)*ClassicalSixthBranch.v ((641629577:ℝ)/168755200)/ClassicalSixthBranch.r = (102091546783457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2603
  · change upperPayment 2604 ≤ upperValue ((point split endpoint 4096 2604+point split endpoint 4096 2605)/2)
    have hp : upperPayment 2604 = (209481856800:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2604+point split endpoint 4096 2605)/2 = (641654727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641654727:ℝ)/168755200)*ClassicalSixthBranch.v ((641654727:ℝ)/168755200)/ClassicalSixthBranch.r = (102070800150081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2604
  · change upperPayment 2605 ≤ upperValue ((point split endpoint 4096 2605+point split endpoint 4096 2606)/2)
    have hp : upperPayment 2605 = (209366449552:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2605+point split endpoint 4096 2606)/2 = (641679877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641679877:ℝ)/168755200)*ClassicalSixthBranch.v ((641679877:ℝ)/168755200)/ClassicalSixthBranch.r = (102050055540777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2605
  · change upperPayment 2606 ≤ upperValue ((point split endpoint 4096 2606+point split endpoint 4096 2607)/2)
    have hp : upperPayment 2606 = (209251012538:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2606+point split endpoint 4096 2607)/2 = (641705027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641705027:ℝ)/168755200)*ClassicalSixthBranch.v ((641705027:ℝ)/168755200)/ClassicalSixthBranch.r = (102029312955545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2606
  · change upperPayment 2607 ≤ upperValue ((point split endpoint 4096 2607+point split endpoint 4096 2608)/2)
    have hp : upperPayment 2607 = (209135545753:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2607+point split endpoint 4096 2608)/2 = (641730177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641730177:ℝ)/168755200)*ClassicalSixthBranch.v ((641730177:ℝ)/168755200)/ClassicalSixthBranch.r = (102008572394385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2607
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_162
