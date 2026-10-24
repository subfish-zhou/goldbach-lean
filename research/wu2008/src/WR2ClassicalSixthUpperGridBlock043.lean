import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints043
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_043 (j : Fin 16) : upperPayment (16*43+j.val) ≤
    upperValue ((point split endpoint 4096 (16*43+j.val)+point split endpoint 4096 (16*43+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 688 ≤ upperValue ((point split endpoint 4096 688+point split endpoint 4096 689)/2)
    have hp : upperPayment 688 = (382394811714:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 688+point split endpoint 4096 689)/2 = (593467327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593467327:ℝ)/168755200)*ClassicalSixthBranch.v ((593467327:ℝ)/168755200)/ClassicalSixthBranch.r = (145534651467537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_688
  · change upperPayment 689 ≤ upperValue ((point split endpoint 4096 689+point split endpoint 4096 690)/2)
    have hp : upperPayment 689 = (382326921810:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 689+point split endpoint 4096 690)/2 = (593492477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593492477:ℝ)/168755200)*ClassicalSixthBranch.v ((593492477:ℝ)/168755200)/ClassicalSixthBranch.r = (145510028736281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_689
  · change upperPayment 690 ≤ upperValue ((point split endpoint 4096 690+point split endpoint 4096 691)/2)
    have hp : upperPayment 690 = (382259010919:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 690+point split endpoint 4096 691)/2 = (593517627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593517627:ℝ)/168755200)*ClassicalSixthBranch.v ((593517627:ℝ)/168755200)/ClassicalSixthBranch.r = (145485408029097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_690
  · change upperPayment 691 ≤ upperValue ((point split endpoint 4096 691+point split endpoint 4096 692)/2)
    have hp : upperPayment 691 = (382191079040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 691+point split endpoint 4096 692)/2 = (593542777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593542777:ℝ)/168755200)*ClassicalSixthBranch.v ((593542777:ℝ)/168755200)/ClassicalSixthBranch.r = (145460789345985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_691
  · change upperPayment 692 ≤ upperValue ((point split endpoint 4096 692+point split endpoint 4096 693)/2)
    have hp : upperPayment 692 = (382123126169:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 692+point split endpoint 4096 693)/2 = (593567927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593567927:ℝ)/168755200)*ClassicalSixthBranch.v ((593567927:ℝ)/168755200)/ClassicalSixthBranch.r = (145436172686945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_692
  · change upperPayment 693 ≤ upperValue ((point split endpoint 4096 693+point split endpoint 4096 694)/2)
    have hp : upperPayment 693 = (382055152303:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 693+point split endpoint 4096 694)/2 = (593593077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593593077:ℝ)/168755200)*ClassicalSixthBranch.v ((593593077:ℝ)/168755200)/ClassicalSixthBranch.r = (145411558051977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_693
  · change upperPayment 694 ≤ upperValue ((point split endpoint 4096 694+point split endpoint 4096 695)/2)
    have hp : upperPayment 694 = (381987157440:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 694+point split endpoint 4096 695)/2 = (593618227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593618227:ℝ)/168755200)*ClassicalSixthBranch.v ((593618227:ℝ)/168755200)/ClassicalSixthBranch.r = (145386945441081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_694
  · change upperPayment 695 ≤ upperValue ((point split endpoint 4096 695+point split endpoint 4096 696)/2)
    have hp : upperPayment 695 = (381919141576:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 695+point split endpoint 4096 696)/2 = (593643377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593643377:ℝ)/168755200)*ClassicalSixthBranch.v ((593643377:ℝ)/168755200)/ClassicalSixthBranch.r = (145362334854257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_695
  · change upperPayment 696 ≤ upperValue ((point split endpoint 4096 696+point split endpoint 4096 697)/2)
    have hp : upperPayment 696 = (381851104709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 696+point split endpoint 4096 697)/2 = (593668527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593668527:ℝ)/168755200)*ClassicalSixthBranch.v ((593668527:ℝ)/168755200)/ClassicalSixthBranch.r = (145337726291505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_696
  · change upperPayment 697 ≤ upperValue ((point split endpoint 4096 697+point split endpoint 4096 698)/2)
    have hp : upperPayment 697 = (381783046835:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 697+point split endpoint 4096 698)/2 = (593693677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593693677:ℝ)/168755200)*ClassicalSixthBranch.v ((593693677:ℝ)/168755200)/ClassicalSixthBranch.r = (145313119752825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_697
  · change upperPayment 698 ≤ upperValue ((point split endpoint 4096 698+point split endpoint 4096 699)/2)
    have hp : upperPayment 698 = (381714967951:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 698+point split endpoint 4096 699)/2 = (593718827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593718827:ℝ)/168755200)*ClassicalSixthBranch.v ((593718827:ℝ)/168755200)/ClassicalSixthBranch.r = (145288515238217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_698
  · change upperPayment 699 ≤ upperValue ((point split endpoint 4096 699+point split endpoint 4096 700)/2)
    have hp : upperPayment 699 = (381646868055:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 699+point split endpoint 4096 700)/2 = (593743977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593743977:ℝ)/168755200)*ClassicalSixthBranch.v ((593743977:ℝ)/168755200)/ClassicalSixthBranch.r = (145263912747681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_699
  · change upperPayment 700 ≤ upperValue ((point split endpoint 4096 700+point split endpoint 4096 701)/2)
    have hp : upperPayment 700 = (381578747144:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 700+point split endpoint 4096 701)/2 = (593769127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593769127:ℝ)/168755200)*ClassicalSixthBranch.v ((593769127:ℝ)/168755200)/ClassicalSixthBranch.r = (145239312281217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_700
  · change upperPayment 701 ≤ upperValue ((point split endpoint 4096 701+point split endpoint 4096 702)/2)
    have hp : upperPayment 701 = (381510605214:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 701+point split endpoint 4096 702)/2 = (593794277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593794277:ℝ)/168755200)*ClassicalSixthBranch.v ((593794277:ℝ)/168755200)/ClassicalSixthBranch.r = (145214713838825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_701
  · change upperPayment 702 ≤ upperValue ((point split endpoint 4096 702+point split endpoint 4096 703)/2)
    have hp : upperPayment 702 = (381442442263:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 702+point split endpoint 4096 703)/2 = (593819427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593819427:ℝ)/168755200)*ClassicalSixthBranch.v ((593819427:ℝ)/168755200)/ClassicalSixthBranch.r = (145190117420505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_702
  · change upperPayment 703 ≤ upperValue ((point split endpoint 4096 703+point split endpoint 4096 704)/2)
    have hp : upperPayment 703 = (381374258287:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 703+point split endpoint 4096 704)/2 = (593844577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593844577:ℝ)/168755200)*ClassicalSixthBranch.v ((593844577:ℝ)/168755200)/ClassicalSixthBranch.r = (145165523026257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_703
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_043
