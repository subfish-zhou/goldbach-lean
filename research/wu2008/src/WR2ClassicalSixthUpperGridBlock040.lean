import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints040
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_040 (j : Fin 16) : upperPayment (16*40+j.val) ≤
    upperValue ((point split endpoint 4096 (16*40+j.val)+point split endpoint 4096 (16*40+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 640 ≤ upperValue ((point split endpoint 4096 640+point split endpoint 4096 641)/2)
    have hp : upperPayment 640 = (385628905754:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 640+point split endpoint 4096 641)/2 = (592260127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592260127:ℝ)/168755200)*ClassicalSixthBranch.v ((592260127:ℝ)/168755200)/ClassicalSixthBranch.r = (146718922876497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_640
  · change upperPayment 641 ≤ upperValue ((point split endpoint 4096 641+point split endpoint 4096 642)/2)
    have hp : upperPayment 641 = (385562019701:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 641+point split endpoint 4096 642)/2 = (592285277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592285277:ℝ)/168755200)*ClassicalSixthBranch.v ((592285277:ℝ)/168755200)/ClassicalSixthBranch.r = (146694202989785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_641
  · change upperPayment 642 ≤ upperValue ((point split endpoint 4096 642+point split endpoint 4096 643)/2)
    have hp : upperPayment 642 = (385495112803:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 642+point split endpoint 4096 643)/2 = (592310427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592310427:ℝ)/168755200)*ClassicalSixthBranch.v ((592310427:ℝ)/168755200)/ClassicalSixthBranch.r = (146669485127145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_642
  · change upperPayment 643 ≤ upperValue ((point split endpoint 4096 643+point split endpoint 4096 644)/2)
    have hp : upperPayment 643 = (385428185057:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 643+point split endpoint 4096 644)/2 = (592335577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592335577:ℝ)/168755200)*ClassicalSixthBranch.v ((592335577:ℝ)/168755200)/ClassicalSixthBranch.r = (146644769288577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_643
  · change upperPayment 644 ≤ upperValue ((point split endpoint 4096 644+point split endpoint 4096 645)/2)
    have hp : upperPayment 644 = (385361236460:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 644+point split endpoint 4096 645)/2 = (592360727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592360727:ℝ)/168755200)*ClassicalSixthBranch.v ((592360727:ℝ)/168755200)/ClassicalSixthBranch.r = (146620055474081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_644
  · change upperPayment 645 ≤ upperValue ((point split endpoint 4096 645+point split endpoint 4096 646)/2)
    have hp : upperPayment 645 = (385294267010:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 645+point split endpoint 4096 646)/2 = (592385877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592385877:ℝ)/168755200)*ClassicalSixthBranch.v ((592385877:ℝ)/168755200)/ClassicalSixthBranch.r = (1423255763919:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_645
  · change upperPayment 646 ≤ upperValue ((point split endpoint 4096 646+point split endpoint 4096 647)/2)
    have hp : upperPayment 646 = (385227276703:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 646+point split endpoint 4096 647)/2 = (592411027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592411027:ℝ)/168755200)*ClassicalSixthBranch.v ((592411027:ℝ)/168755200)/ClassicalSixthBranch.r = (146570633917305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_646
  · change upperPayment 647 ≤ upperValue ((point split endpoint 4096 647+point split endpoint 4096 648)/2)
    have hp : upperPayment 647 = (385160265537:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 647+point split endpoint 4096 648)/2 = (592436177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592436177:ℝ)/168755200)*ClassicalSixthBranch.v ((592436177:ℝ)/168755200)/ClassicalSixthBranch.r = (146545926175025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_647
  · change upperPayment 648 ≤ upperValue ((point split endpoint 4096 648+point split endpoint 4096 649)/2)
    have hp : upperPayment 648 = (385093233509:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 648+point split endpoint 4096 649)/2 = (592461327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592461327:ℝ)/168755200)*ClassicalSixthBranch.v ((592461327:ℝ)/168755200)/ClassicalSixthBranch.r = (146521220456817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_648
  · change upperPayment 649 ≤ upperValue ((point split endpoint 4096 649+point split endpoint 4096 650)/2)
    have hp : upperPayment 649 = (385026180615:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 649+point split endpoint 4096 650)/2 = (592486477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592486477:ℝ)/168755200)*ClassicalSixthBranch.v ((592486477:ℝ)/168755200)/ClassicalSixthBranch.r = (146496516762681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_649
  · change upperPayment 650 ≤ upperValue ((point split endpoint 4096 650+point split endpoint 4096 651)/2)
    have hp : upperPayment 650 = (384959106853:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 650+point split endpoint 4096 651)/2 = (592511627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592511627:ℝ)/168755200)*ClassicalSixthBranch.v ((592511627:ℝ)/168755200)/ClassicalSixthBranch.r = (146471815092617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_650
  · change upperPayment 651 ≤ upperValue ((point split endpoint 4096 651+point split endpoint 4096 652)/2)
    have hp : upperPayment 651 = (384892012221:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 651+point split endpoint 4096 652)/2 = (592536777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592536777:ℝ)/168755200)*ClassicalSixthBranch.v ((592536777:ℝ)/168755200)/ClassicalSixthBranch.r = (146447115446625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_651
  · change upperPayment 652 ≤ upperValue ((point split endpoint 4096 652+point split endpoint 4096 653)/2)
    have hp : upperPayment 652 = (384824896714:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 652+point split endpoint 4096 653)/2 = (592561927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592561927:ℝ)/168755200)*ClassicalSixthBranch.v ((592561927:ℝ)/168755200)/ClassicalSixthBranch.r = (146422417824705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_652
  · change upperPayment 653 ≤ upperValue ((point split endpoint 4096 653+point split endpoint 4096 654)/2)
    have hp : upperPayment 653 = (384757760330:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 653+point split endpoint 4096 654)/2 = (592587077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592587077:ℝ)/168755200)*ClassicalSixthBranch.v ((592587077:ℝ)/168755200)/ClassicalSixthBranch.r = (146397722226857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_653
  · change upperPayment 654 ≤ upperValue ((point split endpoint 4096 654+point split endpoint 4096 655)/2)
    have hp : upperPayment 654 = (384690603067:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 654+point split endpoint 4096 655)/2 = (592612227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592612227:ℝ)/168755200)*ClassicalSixthBranch.v ((592612227:ℝ)/168755200)/ClassicalSixthBranch.r = (146373028653081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_654
  · change upperPayment 655 ≤ upperValue ((point split endpoint 4096 655+point split endpoint 4096 656)/2)
    have hp : upperPayment 655 = (384623424921:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 655+point split endpoint 4096 656)/2 = (592637377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592637377:ℝ)/168755200)*ClassicalSixthBranch.v ((592637377:ℝ)/168755200)/ClassicalSixthBranch.r = (146348337103377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_655
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_040
