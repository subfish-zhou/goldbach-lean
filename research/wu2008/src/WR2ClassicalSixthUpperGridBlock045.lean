import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints045
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_045 (j : Fin 16) : upperPayment (16*45+j.val) ≤
    upperValue ((point split endpoint 4096 (16*45+j.val)+point split endpoint 4096 (16*45+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 720 ≤ upperValue ((point split endpoint 4096 720+point split endpoint 4096 721)/2)
    have hp : upperPayment 720 = (380211911061:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 720+point split endpoint 4096 721)/2 = (594272127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594272127:ℝ)/168755200)*ClassicalSixthBranch.v ((594272127:ℝ)/168755200)/ClassicalSixthBranch.r = (144747728007057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_720
  · change upperPayment 721 ≤ upperValue ((point split endpoint 4096 721+point split endpoint 4096 722)/2)
    have hp : upperPayment 721 = (380143348134:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 721+point split endpoint 4096 722)/2 = (594297277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594297277:ℝ)/168755200)*ClassicalSixthBranch.v ((594297277:ℝ)/168755200)/ClassicalSixthBranch.r = (144723170046105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_721
  · change upperPayment 722 ≤ upperValue ((point split endpoint 4096 722+point split endpoint 4096 723)/2)
    have hp : upperPayment 722 = (380074764125:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 722+point split endpoint 4096 723)/2 = (594322427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594322427:ℝ)/168755200)*ClassicalSixthBranch.v ((594322427:ℝ)/168755200)/ClassicalSixthBranch.r = (144698614109225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_722
  · change upperPayment 723 ≤ upperValue ((point split endpoint 4096 723+point split endpoint 4096 724)/2)
    have hp : upperPayment 723 = (380006159031:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 723+point split endpoint 4096 724)/2 = (594347577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594347577:ℝ)/168755200)*ClassicalSixthBranch.v ((594347577:ℝ)/168755200)/ClassicalSixthBranch.r = (144674060196417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_723
  · change upperPayment 724 ≤ upperValue ((point split endpoint 4096 724+point split endpoint 4096 725)/2)
    have hp : upperPayment 724 = (379937532851:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 724+point split endpoint 4096 725)/2 = (5770609:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5770609:ℝ)/1638400)*ClassicalSixthBranch.v ((5770609:ℝ)/1638400)/ClassicalSixthBranch.r = (1404364158327:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_724
  · change upperPayment 725 ≤ upperValue ((point split endpoint 4096 725+point split endpoint 4096 726)/2)
    have hp : upperPayment 725 = (379868885579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 725+point split endpoint 4096 726)/2 = (594397877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594397877:ℝ)/168755200)*ClassicalSixthBranch.v ((594397877:ℝ)/168755200)/ClassicalSixthBranch.r = (144624958443017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_725
  · change upperPayment 726 ≤ upperValue ((point split endpoint 4096 726+point split endpoint 4096 727)/2)
    have hp : upperPayment 726 = (379800217215:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 726+point split endpoint 4096 727)/2 = (594423027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594423027:ℝ)/168755200)*ClassicalSixthBranch.v ((594423027:ℝ)/168755200)/ClassicalSixthBranch.r = (144600410602425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_726
  · change upperPayment 727 ≤ upperValue ((point split endpoint 4096 727+point split endpoint 4096 728)/2)
    have hp : upperPayment 727 = (379731527753:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 727+point split endpoint 4096 728)/2 = (594448177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594448177:ℝ)/168755200)*ClassicalSixthBranch.v ((594448177:ℝ)/168755200)/ClassicalSixthBranch.r = (144575864785905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_727
  · change upperPayment 728 ≤ upperValue ((point split endpoint 4096 728+point split endpoint 4096 729)/2)
    have hp : upperPayment 728 = (379662817193:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 728+point split endpoint 4096 729)/2 = (594473327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594473327:ℝ)/168755200)*ClassicalSixthBranch.v ((594473327:ℝ)/168755200)/ClassicalSixthBranch.r = (144551320993457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_728
  · change upperPayment 729 ≤ upperValue ((point split endpoint 4096 729+point split endpoint 4096 730)/2)
    have hp : upperPayment 729 = (379594085529:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 729+point split endpoint 4096 730)/2 = (594498477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594498477:ℝ)/168755200)*ClassicalSixthBranch.v ((594498477:ℝ)/168755200)/ClassicalSixthBranch.r = (144526779225081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_729
  · change upperPayment 730 ≤ upperValue ((point split endpoint 4096 730+point split endpoint 4096 731)/2)
    have hp : upperPayment 730 = (379525332761:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 730+point split endpoint 4096 731)/2 = (594523627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594523627:ℝ)/168755200)*ClassicalSixthBranch.v ((594523627:ℝ)/168755200)/ClassicalSixthBranch.r = (144502239480777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_730
  · change upperPayment 731 ≤ upperValue ((point split endpoint 4096 731+point split endpoint 4096 732)/2)
    have hp : upperPayment 731 = (379456558883:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 731+point split endpoint 4096 732)/2 = (594548777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594548777:ℝ)/168755200)*ClassicalSixthBranch.v ((594548777:ℝ)/168755200)/ClassicalSixthBranch.r = (144477701760545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_731
  · change upperPayment 732 ≤ upperValue ((point split endpoint 4096 732+point split endpoint 4096 733)/2)
    have hp : upperPayment 732 = (379387763894:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 732+point split endpoint 4096 733)/2 = (594573927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594573927:ℝ)/168755200)*ClassicalSixthBranch.v ((594573927:ℝ)/168755200)/ClassicalSixthBranch.r = (144453166064385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_732
  · change upperPayment 733 ≤ upperValue ((point split endpoint 4096 733+point split endpoint 4096 734)/2)
    have hp : upperPayment 733 = (379318947791:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 733+point split endpoint 4096 734)/2 = (594599077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594599077:ℝ)/168755200)*ClassicalSixthBranch.v ((594599077:ℝ)/168755200)/ClassicalSixthBranch.r = (144428632392297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_733
  · change upperPayment 734 ≤ upperValue ((point split endpoint 4096 734+point split endpoint 4096 735)/2)
    have hp : upperPayment 734 = (379250110570:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 734+point split endpoint 4096 735)/2 = (594624227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594624227:ℝ)/168755200)*ClassicalSixthBranch.v ((594624227:ℝ)/168755200)/ClassicalSixthBranch.r = (144404100744281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_734
  · change upperPayment 735 ≤ upperValue ((point split endpoint 4096 735+point split endpoint 4096 736)/2)
    have hp : upperPayment 735 = (379181252228:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 735+point split endpoint 4096 736)/2 = (594649377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594649377:ℝ)/168755200)*ClassicalSixthBranch.v ((594649377:ℝ)/168755200)/ClassicalSixthBranch.r = (144379571120337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_735
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_045
