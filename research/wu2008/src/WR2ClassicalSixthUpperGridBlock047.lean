import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints047
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_047 (j : Fin 16) : upperPayment (16*47+j.val) ≤
    upperValue ((point split endpoint 4096 (16*47+j.val)+point split endpoint 4096 (16*47+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 752 ≤ upperValue ((point split endpoint 4096 752+point split endpoint 4096 753)/2)
    have hp : upperPayment 752 = (378007426012:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 752+point split endpoint 4096 753)/2 = (595076927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595076927:ℝ)/168755200)*ClassicalSixthBranch.v ((595076927:ℝ)/168755200)/ClassicalSixthBranch.r = (143962877196305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_752
  · change upperPayment 753 ≤ upperValue ((point split endpoint 4096 753+point split endpoint 4096 754)/2)
    have hp : upperPayment 753 = (377938186978:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 753+point split endpoint 4096 754)/2 = (595102077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595102077:ℝ)/168755200)*ClassicalSixthBranch.v ((595102077:ℝ)/168755200)/ClassicalSixthBranch.r = (143938384005657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_753
  · change upperPayment 754 ≤ upperValue ((point split endpoint 4096 754+point split endpoint 4096 755)/2)
    have hp : upperPayment 754 = (377868926766:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 754+point split endpoint 4096 755)/2 = (595127227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595127227:ℝ)/168755200)*ClassicalSixthBranch.v ((595127227:ℝ)/168755200)/ClassicalSixthBranch.r = (143913892839081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_754
  · change upperPayment 755 ≤ upperValue ((point split endpoint 4096 755+point split endpoint 4096 756)/2)
    have hp : upperPayment 755 = (377799645373:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 755+point split endpoint 4096 756)/2 = (595152377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595152377:ℝ)/168755200)*ClassicalSixthBranch.v ((595152377:ℝ)/168755200)/ClassicalSixthBranch.r = (143889403696577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_755
  · change upperPayment 756 ≤ upperValue ((point split endpoint 4096 756+point split endpoint 4096 757)/2)
    have hp : upperPayment 756 = (377730342795:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 756+point split endpoint 4096 757)/2 = (595177527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595177527:ℝ)/168755200)*ClassicalSixthBranch.v ((595177527:ℝ)/168755200)/ClassicalSixthBranch.r = (143864916578145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_756
  · change upperPayment 757 ≤ upperValue ((point split endpoint 4096 757+point split endpoint 4096 758)/2)
    have hp : upperPayment 757 = (377661019029:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 757+point split endpoint 4096 758)/2 = (595202677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595202677:ℝ)/168755200)*ClassicalSixthBranch.v ((595202677:ℝ)/168755200)/ClassicalSixthBranch.r = (143840431483785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_757
  · change upperPayment 758 ≤ upperValue ((point split endpoint 4096 758+point split endpoint 4096 759)/2)
    have hp : upperPayment 758 = (377591674072:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 758+point split endpoint 4096 759)/2 = (595227827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595227827:ℝ)/168755200)*ClassicalSixthBranch.v ((595227827:ℝ)/168755200)/ClassicalSixthBranch.r = (143815948413497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_758
  · change upperPayment 759 ≤ upperValue ((point split endpoint 4096 759+point split endpoint 4096 760)/2)
    have hp : upperPayment 759 = (377522307922:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 759+point split endpoint 4096 760)/2 = (595252977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595252977:ℝ)/168755200)*ClassicalSixthBranch.v ((595252977:ℝ)/168755200)/ClassicalSixthBranch.r = (143791467367281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_759
  · change upperPayment 760 ≤ upperValue ((point split endpoint 4096 760+point split endpoint 4096 761)/2)
    have hp : upperPayment 760 = (377452920575:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 760+point split endpoint 4096 761)/2 = (595278127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595278127:ℝ)/168755200)*ClassicalSixthBranch.v ((595278127:ℝ)/168755200)/ClassicalSixthBranch.r = (143766988345137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_760
  · change upperPayment 761 ≤ upperValue ((point split endpoint 4096 761+point split endpoint 4096 762)/2)
    have hp : upperPayment 761 = (377383512028:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 761+point split endpoint 4096 762)/2 = (595303277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595303277:ℝ)/168755200)*ClassicalSixthBranch.v ((595303277:ℝ)/168755200)/ClassicalSixthBranch.r = (143742511347065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_761
  · change upperPayment 762 ≤ upperValue ((point split endpoint 4096 762+point split endpoint 4096 763)/2)
    have hp : upperPayment 762 = (377314082278:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 762+point split endpoint 4096 763)/2 = (595328427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595328427:ℝ)/168755200)*ClassicalSixthBranch.v ((595328427:ℝ)/168755200)/ClassicalSixthBranch.r = (143718036373065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_762
  · change upperPayment 763 ≤ upperValue ((point split endpoint 4096 763+point split endpoint 4096 764)/2)
    have hp : upperPayment 763 = (377244631322:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 763+point split endpoint 4096 764)/2 = (595353577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595353577:ℝ)/168755200)*ClassicalSixthBranch.v ((595353577:ℝ)/168755200)/ClassicalSixthBranch.r = (143693563423137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_763
  · change upperPayment 764 ≤ upperValue ((point split endpoint 4096 764+point split endpoint 4096 765)/2)
    have hp : upperPayment 764 = (377175159157:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 764+point split endpoint 4096 765)/2 = (595378727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595378727:ℝ)/168755200)*ClassicalSixthBranch.v ((595378727:ℝ)/168755200)/ClassicalSixthBranch.r = (143669092497281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_764
  · change upperPayment 765 ≤ upperValue ((point split endpoint 4096 765+point split endpoint 4096 766)/2)
    have hp : upperPayment 765 = (377105665779:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 765+point split endpoint 4096 766)/2 = (595403877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595403877:ℝ)/168755200)*ClassicalSixthBranch.v ((595403877:ℝ)/168755200)/ClassicalSixthBranch.r = (143644623595497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_765
  · change upperPayment 766 ≤ upperValue ((point split endpoint 4096 766+point split endpoint 4096 767)/2)
    have hp : upperPayment 766 = (377036151187:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 766+point split endpoint 4096 767)/2 = (595429027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595429027:ℝ)/168755200)*ClassicalSixthBranch.v ((595429027:ℝ)/168755200)/ClassicalSixthBranch.r = (143620156717785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_766
  · change upperPayment 767 ≤ upperValue ((point split endpoint 4096 767+point split endpoint 4096 768)/2)
    have hp : upperPayment 767 = (376966615376:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 767+point split endpoint 4096 768)/2 = (595454177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595454177:ℝ)/168755200)*ClassicalSixthBranch.v ((595454177:ℝ)/168755200)/ClassicalSixthBranch.r = (143595691864145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_767
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_047
