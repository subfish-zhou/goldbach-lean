import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints227
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_227 (j : Fin 16) : upperPayment (16*227+j.val) ≤
    upperValue ((point split endpoint 4096 (16*227+j.val)+point split endpoint 4096 (16*227+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3632 ≤ upperValue ((point split endpoint 4096 3632+point split endpoint 4096 3633)/2)
    have hp : upperPayment 3632 = (73804660084:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3632+point split endpoint 4096 3633)/2 = (667508927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667508927:ℝ)/168755200)*ClassicalSixthBranch.v ((667508927:ℝ)/168755200)/ClassicalSixthBranch.r = (794308785095:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3632
  · change upperPayment 3633 ≤ upperValue ((point split endpoint 4096 3633+point split endpoint 4096 3634)/2)
    have hp : upperPayment 3633 = (73654632660:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3633+point split endpoint 4096 3634)/2 = (667534077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667534077:ℝ)/168755200)*ClassicalSixthBranch.v ((667534077:ℝ)/168755200)/ClassicalSixthBranch.r = (81795141001497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3633
  · change upperPayment 3634 ≤ upperValue ((point split endpoint 4096 3634+point split endpoint 4096 3635)/2)
    have hp : upperPayment 3634 = (73504567050:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3634+point split endpoint 4096 3635)/2 = (667559227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667559227:ℝ)/168755200)*ClassicalSixthBranch.v ((667559227:ℝ)/168755200)/ClassicalSixthBranch.r = (81776479162281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3634
  · change upperPayment 3635 ≤ upperValue ((point split endpoint 4096 3635+point split endpoint 4096 3636)/2)
    have hp : upperPayment 3635 = (73354463245:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3635+point split endpoint 4096 3636)/2 = (667584377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667584377:ℝ)/168755200)*ClassicalSixthBranch.v ((667584377:ℝ)/168755200)/ClassicalSixthBranch.r = (81757819347137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3635
  · change upperPayment 3636 ≤ upperValue ((point split endpoint 4096 3636+point split endpoint 4096 3637)/2)
    have hp : upperPayment 3636 = (73204321235:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3636+point split endpoint 4096 3637)/2 = (667609527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667609527:ℝ)/168755200)*ClassicalSixthBranch.v ((667609527:ℝ)/168755200)/ClassicalSixthBranch.r = (81739161556065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3636
  · change upperPayment 3637 ≤ upperValue ((point split endpoint 4096 3637+point split endpoint 4096 3638)/2)
    have hp : upperPayment 3637 = (73054141010:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3637+point split endpoint 4096 3638)/2 = (667634677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667634677:ℝ)/168755200)*ClassicalSixthBranch.v ((667634677:ℝ)/168755200)/ClassicalSixthBranch.r = (81720505789065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3637
  · change upperPayment 3638 ≤ upperValue ((point split endpoint 4096 3638+point split endpoint 4096 3639)/2)
    have hp : upperPayment 3638 = (72903922560:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3638+point split endpoint 4096 3639)/2 = (667659827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667659827:ℝ)/168755200)*ClassicalSixthBranch.v ((667659827:ℝ)/168755200)/ClassicalSixthBranch.r = (81701852046137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3638
  · change upperPayment 3639 ≤ upperValue ((point split endpoint 4096 3639+point split endpoint 4096 3640)/2)
    have hp : upperPayment 3639 = (72753665874:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3639+point split endpoint 4096 3640)/2 = (667684977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667684977:ℝ)/168755200)*ClassicalSixthBranch.v ((667684977:ℝ)/168755200)/ClassicalSixthBranch.r = (81683200327281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3639
  · change upperPayment 3640 ≤ upperValue ((point split endpoint 4096 3640+point split endpoint 4096 3641)/2)
    have hp : upperPayment 3640 = (72603370943:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3640+point split endpoint 4096 3641)/2 = (667710127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667710127:ℝ)/168755200)*ClassicalSixthBranch.v ((667710127:ℝ)/168755200)/ClassicalSixthBranch.r = (81664550632497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3640
  · change upperPayment 3641 ≤ upperValue ((point split endpoint 4096 3641+point split endpoint 4096 3642)/2)
    have hp : upperPayment 3641 = (72453037756:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3641+point split endpoint 4096 3642)/2 = (667735277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667735277:ℝ)/168755200)*ClassicalSixthBranch.v ((667735277:ℝ)/168755200)/ClassicalSixthBranch.r = (81645902961785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3641
  · change upperPayment 3642 ≤ upperValue ((point split endpoint 4096 3642+point split endpoint 4096 3643)/2)
    have hp : upperPayment 3642 = (72302666304:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3642+point split endpoint 4096 3643)/2 = (667760427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667760427:ℝ)/168755200)*ClassicalSixthBranch.v ((667760427:ℝ)/168755200)/ClassicalSixthBranch.r = (81627257315145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3642
  · change upperPayment 3643 ≤ upperValue ((point split endpoint 4096 3643+point split endpoint 4096 3644)/2)
    have hp : upperPayment 3643 = (72152256576:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3643+point split endpoint 4096 3644)/2 = (667785577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667785577:ℝ)/168755200)*ClassicalSixthBranch.v ((667785577:ℝ)/168755200)/ClassicalSixthBranch.r = (81608613692577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3643
  · change upperPayment 3644 ≤ upperValue ((point split endpoint 4096 3644+point split endpoint 4096 3645)/2)
    have hp : upperPayment 3644 = (72001808562:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3644+point split endpoint 4096 3645)/2 = (667810727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667810727:ℝ)/168755200)*ClassicalSixthBranch.v ((667810727:ℝ)/168755200)/ClassicalSixthBranch.r = (81589972094081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3644
  · change upperPayment 3645 ≤ upperValue ((point split endpoint 4096 3645+point split endpoint 4096 3646)/2)
    have hp : upperPayment 3645 = (71851322253:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3645+point split endpoint 4096 3646)/2 = (667835877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667835877:ℝ)/168755200)*ClassicalSixthBranch.v ((667835877:ℝ)/168755200)/ClassicalSixthBranch.r = (81571332519657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3645
  · change upperPayment 3646 ≤ upperValue ((point split endpoint 4096 3646+point split endpoint 4096 3647)/2)
    have hp : upperPayment 3646 = (71700797637:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3646+point split endpoint 4096 3647)/2 = (667861027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667861027:ℝ)/168755200)*ClassicalSixthBranch.v ((667861027:ℝ)/168755200)/ClassicalSixthBranch.r = (81552694969305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3646
  · change upperPayment 3647 ≤ upperValue ((point split endpoint 4096 3647+point split endpoint 4096 3648)/2)
    have hp : upperPayment 3647 = (71550234706:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3647+point split endpoint 4096 3648)/2 = (667886177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667886177:ℝ)/168755200)*ClassicalSixthBranch.v ((667886177:ℝ)/168755200)/ClassicalSixthBranch.r = (81534059443025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3647
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_227
