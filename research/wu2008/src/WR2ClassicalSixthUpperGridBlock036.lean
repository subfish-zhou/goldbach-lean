import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints036
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_036 (j : Fin 16) : upperPayment (16*36+j.val) ≤
    upperValue ((point split endpoint 4096 (16*36+j.val)+point split endpoint 4096 (16*36+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 576 ≤ upperValue ((point split endpoint 4096 576+point split endpoint 4096 577)/2)
    have hp : upperPayment 576 = (389866387681:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 576+point split endpoint 4096 577)/2 = (590650527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590650527:ℝ)/168755200)*ClassicalSixthBranch.v ((590650527:ℝ)/168755200)/ClassicalSixthBranch.r = (148305205695825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_576
  · change upperPayment 577 ≤ upperValue ((point split endpoint 4096 577+point split endpoint 4096 578)/2)
    have hp : upperPayment 577 = (389800829722:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 577+point split endpoint 4096 578)/2 = (590675677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590675677:ℝ)/168755200)*ClassicalSixthBranch.v ((590675677:ℝ)/168755200)/ClassicalSixthBranch.r = (148280356268505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_577
  · change upperPayment 578 ≤ upperValue ((point split endpoint 4096 578+point split endpoint 4096 579)/2)
    have hp : upperPayment 578 = (389735251100:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 578+point split endpoint 4096 579)/2 = (590700827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590700827:ℝ)/168755200)*ClassicalSixthBranch.v ((590700827:ℝ)/168755200)/ClassicalSixthBranch.r = (148255508865257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_578
  · change upperPayment 579 ≤ upperValue ((point split endpoint 4096 579+point split endpoint 4096 580)/2)
    have hp : upperPayment 579 = (389669651814:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 579+point split endpoint 4096 580)/2 = (590725977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590725977:ℝ)/168755200)*ClassicalSixthBranch.v ((590725977:ℝ)/168755200)/ClassicalSixthBranch.r = (148230663486081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_579
  · change upperPayment 580 ≤ upperValue ((point split endpoint 4096 580+point split endpoint 4096 581)/2)
    have hp : upperPayment 580 = (389604031861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 580+point split endpoint 4096 581)/2 = (590751127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590751127:ℝ)/168755200)*ClassicalSixthBranch.v ((590751127:ℝ)/168755200)/ClassicalSixthBranch.r = (148205820130977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_580
  · change upperPayment 581 ≤ upperValue ((point split endpoint 4096 581+point split endpoint 4096 582)/2)
    have hp : upperPayment 581 = (389538391237:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 581+point split endpoint 4096 582)/2 = (590776277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590776277:ℝ)/168755200)*ClassicalSixthBranch.v ((590776277:ℝ)/168755200)/ClassicalSixthBranch.r = (148180978799945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_581
  · change upperPayment 582 ≤ upperValue ((point split endpoint 4096 582+point split endpoint 4096 583)/2)
    have hp : upperPayment 582 = (389472729940:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 582+point split endpoint 4096 583)/2 = (590801427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590801427:ℝ)/168755200)*ClassicalSixthBranch.v ((590801427:ℝ)/168755200)/ClassicalSixthBranch.r = (148156139492985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_582
  · change upperPayment 583 ≤ upperValue ((point split endpoint 4096 583+point split endpoint 4096 584)/2)
    have hp : upperPayment 583 = (389407047967:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 583+point split endpoint 4096 584)/2 = (590826577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590826577:ℝ)/168755200)*ClassicalSixthBranch.v ((590826577:ℝ)/168755200)/ClassicalSixthBranch.r = (148131302210097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_583
  · change upperPayment 584 ≤ upperValue ((point split endpoint 4096 584+point split endpoint 4096 585)/2)
    have hp : upperPayment 584 = (389341345316:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 584+point split endpoint 4096 585)/2 = (590851727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590851727:ℝ)/168755200)*ClassicalSixthBranch.v ((590851727:ℝ)/168755200)/ClassicalSixthBranch.r = (148106466951281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_584
  · change upperPayment 585 ≤ upperValue ((point split endpoint 4096 585+point split endpoint 4096 586)/2)
    have hp : upperPayment 585 = (389275621982:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 585+point split endpoint 4096 586)/2 = (590876877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590876877:ℝ)/168755200)*ClassicalSixthBranch.v ((590876877:ℝ)/168755200)/ClassicalSixthBranch.r = (148081633716537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_585
  · change upperPayment 586 ≤ upperValue ((point split endpoint 4096 586+point split endpoint 4096 587)/2)
    have hp : upperPayment 586 = (389209877965:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 586+point split endpoint 4096 587)/2 = (590902027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590902027:ℝ)/168755200)*ClassicalSixthBranch.v ((590902027:ℝ)/168755200)/ClassicalSixthBranch.r = (148056802505865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_586
  · change upperPayment 587 ≤ upperValue ((point split endpoint 4096 587+point split endpoint 4096 588)/2)
    have hp : upperPayment 587 = (389144113260:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 587+point split endpoint 4096 588)/2 = (590927177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590927177:ℝ)/168755200)*ClassicalSixthBranch.v ((590927177:ℝ)/168755200)/ClassicalSixthBranch.r = (148031973319265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_587
  · change upperPayment 588 ≤ upperValue ((point split endpoint 4096 588+point split endpoint 4096 589)/2)
    have hp : upperPayment 588 = (389078327865:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 588+point split endpoint 4096 589)/2 = (590952327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590952327:ℝ)/168755200)*ClassicalSixthBranch.v ((590952327:ℝ)/168755200)/ClassicalSixthBranch.r = (148007146156737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_588
  · change upperPayment 589 ≤ upperValue ((point split endpoint 4096 589+point split endpoint 4096 590)/2)
    have hp : upperPayment 589 = (389012521777:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 589+point split endpoint 4096 590)/2 = (590977477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590977477:ℝ)/168755200)*ClassicalSixthBranch.v ((590977477:ℝ)/168755200)/ClassicalSixthBranch.r = (147982321018281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_589
  · change upperPayment 590 ≤ upperValue ((point split endpoint 4096 590+point split endpoint 4096 591)/2)
    have hp : upperPayment 590 = (388946694993:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 590+point split endpoint 4096 591)/2 = (591002627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591002627:ℝ)/168755200)*ClassicalSixthBranch.v ((591002627:ℝ)/168755200)/ClassicalSixthBranch.r = (147957497903897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_590
  · change upperPayment 591 ≤ upperValue ((point split endpoint 4096 591+point split endpoint 4096 592)/2)
    have hp : upperPayment 591 = (388880847511:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 591+point split endpoint 4096 592)/2 = (591027777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591027777:ℝ)/168755200)*ClassicalSixthBranch.v ((591027777:ℝ)/168755200)/ClassicalSixthBranch.r = (147932676813585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_591
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_036
