import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints237
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_237 (j : Fin 16) : upperPayment (16*237+j.val) ≤
    upperValue ((point split endpoint 4096 (16*237+j.val)+point split endpoint 4096 (16*237+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3792 ≤ upperValue ((point split endpoint 4096 3792+point split endpoint 4096 3793)/2)
    have hp : upperPayment 3792 = (49307712667:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3792+point split endpoint 4096 3793)/2 = (671532927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671532927:ℝ)/168755200)*ClassicalSixthBranch.v ((671532927:ℝ)/168755200)/ClassicalSixthBranch.r = (78853332934545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3792
  · change upperPayment 3793 ≤ upperValue ((point split endpoint 4096 3793+point split endpoint 4096 3794)/2)
    have hp : upperPayment 3793 = (49151444911:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3793+point split endpoint 4096 3794)/2 = (671558077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671558077:ℝ)/168755200)*ClassicalSixthBranch.v ((671558077:ℝ)/168755200)/ClassicalSixthBranch.r = (78834992922777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3793
  · change upperPayment 3794 ≤ upperValue ((point split endpoint 4096 3794+point split endpoint 4096 3795)/2)
    have hp : upperPayment 3794 = (48995137308:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3794+point split endpoint 4096 3795)/2 = (671583227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671583227:ℝ)/168755200)*ClassicalSixthBranch.v ((671583227:ℝ)/168755200)/ClassicalSixthBranch.r = (78816654935081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3794
  · change upperPayment 3795 ≤ upperValue ((point split endpoint 4096 3795+point split endpoint 4096 3796)/2)
    have hp : upperPayment 3795 = (48838789845:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3795+point split endpoint 4096 3796)/2 = (671608377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671608377:ℝ)/168755200)*ClassicalSixthBranch.v ((671608377:ℝ)/168755200)/ClassicalSixthBranch.r = (78798318971457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3795
  · change upperPayment 3796 ≤ upperValue ((point split endpoint 4096 3796+point split endpoint 4096 3797)/2)
    have hp : upperPayment 3796 = (48682402513:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3796+point split endpoint 4096 3797)/2 = (671633527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671633527:ℝ)/168755200)*ClassicalSixthBranch.v ((671633527:ℝ)/168755200)/ClassicalSixthBranch.r = (78779985031905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3796
  · change upperPayment 3797 ≤ upperValue ((point split endpoint 4096 3797+point split endpoint 4096 3798)/2)
    have hp : upperPayment 3797 = (48525975300:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3797+point split endpoint 4096 3798)/2 = (671658677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671658677:ℝ)/168755200)*ClassicalSixthBranch.v ((671658677:ℝ)/168755200)/ClassicalSixthBranch.r = (78761653116425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3797
  · change upperPayment 3798 ≤ upperValue ((point split endpoint 4096 3798+point split endpoint 4096 3799)/2)
    have hp : upperPayment 3798 = (48369508196:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3798+point split endpoint 4096 3799)/2 = (671683827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671683827:ℝ)/168755200)*ClassicalSixthBranch.v ((671683827:ℝ)/168755200)/ClassicalSixthBranch.r = (78743323225017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3798
  · change upperPayment 3799 ≤ upperValue ((point split endpoint 4096 3799+point split endpoint 4096 3800)/2)
    have hp : upperPayment 3799 = (48213001190:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3799+point split endpoint 4096 3800)/2 = (671708977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671708977:ℝ)/168755200)*ClassicalSixthBranch.v ((671708977:ℝ)/168755200)/ClassicalSixthBranch.r = (78724995357681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3799
  · change upperPayment 3800 ≤ upperValue ((point split endpoint 4096 3800+point split endpoint 4096 3801)/2)
    have hp : upperPayment 3800 = (48056454271:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3800+point split endpoint 4096 3801)/2 = (671734127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671734127:ℝ)/168755200)*ClassicalSixthBranch.v ((671734127:ℝ)/168755200)/ClassicalSixthBranch.r = (78706669514417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3800
  · change upperPayment 3801 ≤ upperValue ((point split endpoint 4096 3801+point split endpoint 4096 3802)/2)
    have hp : upperPayment 3801 = (47899867428:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3801+point split endpoint 4096 3802)/2 = (671759277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671759277:ℝ)/168755200)*ClassicalSixthBranch.v ((671759277:ℝ)/168755200)/ClassicalSixthBranch.r = (78688345695225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3801
  · change upperPayment 3802 ≤ upperValue ((point split endpoint 4096 3802+point split endpoint 4096 3803)/2)
    have hp : upperPayment 3802 = (47743240651:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3802+point split endpoint 4096 3803)/2 = (671784427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671784427:ℝ)/168755200)*ClassicalSixthBranch.v ((671784427:ℝ)/168755200)/ClassicalSixthBranch.r = (78670023900105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3802
  · change upperPayment 3803 ≤ upperValue ((point split endpoint 4096 3803+point split endpoint 4096 3804)/2)
    have hp : upperPayment 3803 = (47586573929:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3803+point split endpoint 4096 3804)/2 = (671809577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671809577:ℝ)/168755200)*ClassicalSixthBranch.v ((671809577:ℝ)/168755200)/ClassicalSixthBranch.r = (78651704129057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3803
  · change upperPayment 3804 ≤ upperValue ((point split endpoint 4096 3804+point split endpoint 4096 3805)/2)
    have hp : upperPayment 3804 = (47429867252:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3804+point split endpoint 4096 3805)/2 = (671834727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671834727:ℝ)/168755200)*ClassicalSixthBranch.v ((671834727:ℝ)/168755200)/ClassicalSixthBranch.r = (78633386382081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3804
  · change upperPayment 3805 ≤ upperValue ((point split endpoint 4096 3805+point split endpoint 4096 3806)/2)
    have hp : upperPayment 3805 = (47273120607:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3805+point split endpoint 4096 3806)/2 = (671859877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671859877:ℝ)/168755200)*ClassicalSixthBranch.v ((671859877:ℝ)/168755200)/ClassicalSixthBranch.r = (78615070659177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3805
  · change upperPayment 3806 ≤ upperValue ((point split endpoint 4096 3806+point split endpoint 4096 3807)/2)
    have hp : upperPayment 3806 = (47116333985:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3806+point split endpoint 4096 3807)/2 = (671885027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671885027:ℝ)/168755200)*ClassicalSixthBranch.v ((671885027:ℝ)/168755200)/ClassicalSixthBranch.r = (78596756960345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3806
  · change upperPayment 3807 ≤ upperValue ((point split endpoint 4096 3807+point split endpoint 4096 3808)/2)
    have hp : upperPayment 3807 = (46959507374:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3807+point split endpoint 4096 3808)/2 = (671910177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671910177:ℝ)/168755200)*ClassicalSixthBranch.v ((671910177:ℝ)/168755200)/ClassicalSixthBranch.r = (78578445285585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3807
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_237
