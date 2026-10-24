import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints033
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_033 (j : Fin 16) : upperPayment (16*33+j.val) ≤
    upperValue ((point split endpoint 4096 (16*33+j.val)+point split endpoint 4096 (16*33+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 528 ≤ upperValue ((point split endpoint 4096 528+point split endpoint 4096 529)/2)
    have hp : upperPayment 528 = (392988926299:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 528+point split endpoint 4096 529)/2 = (589443327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589443327:ℝ)/168755200)*ClassicalSixthBranch.v ((589443327:ℝ)/168755200)/ClassicalSixthBranch.r = (149500358515857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_528
  · change upperPayment 529 ≤ upperValue ((point split endpoint 4096 529+point split endpoint 4096 530)/2)
    have hp : upperPayment 529 = (392924356820:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 529+point split endpoint 4096 530)/2 = (589468477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589468477:ℝ)/168755200)*ClassicalSixthBranch.v ((589468477:ℝ)/168755200)/ClassicalSixthBranch.r = (149475411933081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_529
  · change upperPayment 530 ≤ upperValue ((point split endpoint 4096 530+point split endpoint 4096 531)/2)
    have hp : upperPayment 530 = (392859766814:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 530+point split endpoint 4096 531)/2 = (589493627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589493627:ℝ)/168755200)*ClassicalSixthBranch.v ((589493627:ℝ)/168755200)/ClassicalSixthBranch.r = (149450467374377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_530
  · change upperPayment 531 ≤ upperValue ((point split endpoint 4096 531+point split endpoint 4096 532)/2)
    have hp : upperPayment 531 = (392795156276:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 531+point split endpoint 4096 532)/2 = (589518777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589518777:ℝ)/168755200)*ClassicalSixthBranch.v ((589518777:ℝ)/168755200)/ClassicalSixthBranch.r = (149425524839745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_531
  · change upperPayment 532 ≤ upperValue ((point split endpoint 4096 532+point split endpoint 4096 533)/2)
    have hp : upperPayment 532 = (392730525205:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 532+point split endpoint 4096 533)/2 = (589543927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589543927:ℝ)/168755200)*ClassicalSixthBranch.v ((589543927:ℝ)/168755200)/ClassicalSixthBranch.r = (149400584329185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_532
  · change upperPayment 533 ≤ upperValue ((point split endpoint 4096 533+point split endpoint 4096 534)/2)
    have hp : upperPayment 533 = (392665873597:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 533+point split endpoint 4096 534)/2 = (589569077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589569077:ℝ)/168755200)*ClassicalSixthBranch.v ((589569077:ℝ)/168755200)/ClassicalSixthBranch.r = (149375645842697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_533
  · change upperPayment 534 ≤ upperValue ((point split endpoint 4096 534+point split endpoint 4096 535)/2)
    have hp : upperPayment 534 = (392601201451:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 534+point split endpoint 4096 535)/2 = (589594227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589594227:ℝ)/168755200)*ClassicalSixthBranch.v ((589594227:ℝ)/168755200)/ClassicalSixthBranch.r = (149350709380281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_534
  · change upperPayment 535 ≤ upperValue ((point split endpoint 4096 535+point split endpoint 4096 536)/2)
    have hp : upperPayment 535 = (392536508762:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 535+point split endpoint 4096 536)/2 = (589619377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589619377:ℝ)/168755200)*ClassicalSixthBranch.v ((589619377:ℝ)/168755200)/ClassicalSixthBranch.r = (149325774941937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_535
  · change upperPayment 536 ≤ upperValue ((point split endpoint 4096 536+point split endpoint 4096 537)/2)
    have hp : upperPayment 536 = (392471795529:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 536+point split endpoint 4096 537)/2 = (589644527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589644527:ℝ)/168755200)*ClassicalSixthBranch.v ((589644527:ℝ)/168755200)/ClassicalSixthBranch.r = (149300842527665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_536
  · change upperPayment 537 ≤ upperValue ((point split endpoint 4096 537+point split endpoint 4096 538)/2)
    have hp : upperPayment 537 = (392407061748:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 537+point split endpoint 4096 538)/2 = (589669677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589669677:ℝ)/168755200)*ClassicalSixthBranch.v ((589669677:ℝ)/168755200)/ClassicalSixthBranch.r = (149275912137465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_537
  · change upperPayment 538 ≤ upperValue ((point split endpoint 4096 538+point split endpoint 4096 539)/2)
    have hp : upperPayment 538 = (392342307417:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 538+point split endpoint 4096 539)/2 = (589694827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589694827:ℝ)/168755200)*ClassicalSixthBranch.v ((589694827:ℝ)/168755200)/ClassicalSixthBranch.r = (149250983771337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_538
  · change upperPayment 539 ≤ upperValue ((point split endpoint 4096 539+point split endpoint 4096 540)/2)
    have hp : upperPayment 539 = (392277532533:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 539+point split endpoint 4096 540)/2 = (589719977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589719977:ℝ)/168755200)*ClassicalSixthBranch.v ((589719977:ℝ)/168755200)/ClassicalSixthBranch.r = (149226057429281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_539
  · change upperPayment 540 ≤ upperValue ((point split endpoint 4096 540+point split endpoint 4096 541)/2)
    have hp : upperPayment 540 = (392212737093:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 540+point split endpoint 4096 541)/2 = (589745127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589745127:ℝ)/168755200)*ClassicalSixthBranch.v ((589745127:ℝ)/168755200)/ClassicalSixthBranch.r = (149201133111297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_540
  · change upperPayment 541 ≤ upperValue ((point split endpoint 4096 541+point split endpoint 4096 542)/2)
    have hp : upperPayment 541 = (392147921095:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 541+point split endpoint 4096 542)/2 = (589770277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589770277:ℝ)/168755200)*ClassicalSixthBranch.v ((589770277:ℝ)/168755200)/ClassicalSixthBranch.r = (149176210817385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_541
  · change upperPayment 542 ≤ upperValue ((point split endpoint 4096 542+point split endpoint 4096 543)/2)
    have hp : upperPayment 542 = (392083084535:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 542+point split endpoint 4096 543)/2 = (589795427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589795427:ℝ)/168755200)*ClassicalSixthBranch.v ((589795427:ℝ)/168755200)/ClassicalSixthBranch.r = (1448070782015:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_542
  · change upperPayment 543 ≤ upperValue ((point split endpoint 4096 543+point split endpoint 4096 544)/2)
    have hp : upperPayment 543 = (392018227411:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 543+point split endpoint 4096 544)/2 = (589820577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589820577:ℝ)/168755200)*ClassicalSixthBranch.v ((589820577:ℝ)/168755200)/ClassicalSixthBranch.r = (149126372301777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_543
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_033
