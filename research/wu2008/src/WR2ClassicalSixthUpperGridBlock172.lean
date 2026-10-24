import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints172
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_172 (j : Fin 16) : upperPayment (16*172+j.val) ≤
    upperValue ((point split endpoint 4096 (16*172+j.val)+point split endpoint 4096 (16*172+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2752 ≤ upperValue ((point split endpoint 4096 2752+point split endpoint 4096 2753)/2)
    have hp : upperPayment 2752 = (192074249248:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2752+point split endpoint 4096 2753)/2 = (645376927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645376927:ℝ)/168755200)*ClassicalSixthBranch.v ((645376927:ℝ)/168755200)/ClassicalSixthBranch.r = (99022615828305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2752
  · change upperPayment 2753 ≤ upperValue ((point split endpoint 4096 2753+point split endpoint 4096 2754)/2)
    have hp : upperPayment 2753 = (191954363479:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2753+point split endpoint 4096 2754)/2 = (645402077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645402077:ℝ)/168755200)*ClassicalSixthBranch.v ((645402077:ℝ)/168755200)/ClassicalSixthBranch.r = (99002170781657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2753
  · change upperPayment 2754 ≤ upperValue ((point split endpoint 4096 2754+point split endpoint 4096 2755)/2)
    have hp : upperPayment 2754 = (191834446939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2754+point split endpoint 4096 2755)/2 = (645427227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645427227:ℝ)/168755200)*ClassicalSixthBranch.v ((645427227:ℝ)/168755200)/ClassicalSixthBranch.r = (98981727759081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2754
  · change upperPayment 2755 ≤ upperValue ((point split endpoint 4096 2755+point split endpoint 4096 2756)/2)
    have hp : upperPayment 2755 = (191714499620:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2755+point split endpoint 4096 2756)/2 = (645452377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645452377:ℝ)/168755200)*ClassicalSixthBranch.v ((645452377:ℝ)/168755200)/ClassicalSixthBranch.r = (98961286760577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2755
  · change upperPayment 2756 ≤ upperValue ((point split endpoint 4096 2756+point split endpoint 4096 2757)/2)
    have hp : upperPayment 2756 = (191594521515:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2756+point split endpoint 4096 2757)/2 = (645477527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645477527:ℝ)/168755200)*ClassicalSixthBranch.v ((645477527:ℝ)/168755200)/ClassicalSixthBranch.r = (98940847786145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2756
  · change upperPayment 2757 ≤ upperValue ((point split endpoint 4096 2757+point split endpoint 4096 2758)/2)
    have hp : upperPayment 2757 = (191474512617:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2757+point split endpoint 4096 2758)/2 = (645502677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645502677:ℝ)/168755200)*ClassicalSixthBranch.v ((645502677:ℝ)/168755200)/ClassicalSixthBranch.r = (98920410835785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2757
  · change upperPayment 2758 ≤ upperValue ((point split endpoint 4096 2758+point split endpoint 4096 2759)/2)
    have hp : upperPayment 2758 = (191354472919:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2758+point split endpoint 4096 2759)/2 = (645527827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645527827:ℝ)/168755200)*ClassicalSixthBranch.v ((645527827:ℝ)/168755200)/ClassicalSixthBranch.r = (98899975909497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2758
  · change upperPayment 2759 ≤ upperValue ((point split endpoint 4096 2759+point split endpoint 4096 2760)/2)
    have hp : upperPayment 2759 = (191234402414:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2759+point split endpoint 4096 2760)/2 = (645552977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645552977:ℝ)/168755200)*ClassicalSixthBranch.v ((645552977:ℝ)/168755200)/ClassicalSixthBranch.r = (98879543007281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2759
  · change upperPayment 2760 ≤ upperValue ((point split endpoint 4096 2760+point split endpoint 4096 2761)/2)
    have hp : upperPayment 2760 = (191114301096:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2760+point split endpoint 4096 2761)/2 = (645578127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645578127:ℝ)/168755200)*ClassicalSixthBranch.v ((645578127:ℝ)/168755200)/ClassicalSixthBranch.r = (98859112129137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2760
  · change upperPayment 2761 ≤ upperValue ((point split endpoint 4096 2761+point split endpoint 4096 2762)/2)
    have hp : upperPayment 2761 = (190994168956:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2761+point split endpoint 4096 2762)/2 = (645603277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645603277:ℝ)/168755200)*ClassicalSixthBranch.v ((645603277:ℝ)/168755200)/ClassicalSixthBranch.r = (98838683275065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2761
  · change upperPayment 2762 ≤ upperValue ((point split endpoint 4096 2762+point split endpoint 4096 2763)/2)
    have hp : upperPayment 2762 = (190874005989:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2762+point split endpoint 4096 2763)/2 = (645628427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645628427:ℝ)/168755200)*ClassicalSixthBranch.v ((645628427:ℝ)/168755200)/ClassicalSixthBranch.r = (98818256445065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2762
  · change upperPayment 2763 ≤ upperValue ((point split endpoint 4096 2763+point split endpoint 4096 2764)/2)
    have hp : upperPayment 2763 = (190753812186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2763+point split endpoint 4096 2764)/2 = (645653577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645653577:ℝ)/168755200)*ClassicalSixthBranch.v ((645653577:ℝ)/168755200)/ClassicalSixthBranch.r = (98797831639137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2763
  · change upperPayment 2764 ≤ upperValue ((point split endpoint 4096 2764+point split endpoint 4096 2765)/2)
    have hp : upperPayment 2764 = (190633587541:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2764+point split endpoint 4096 2765)/2 = (645678727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645678727:ℝ)/168755200)*ClassicalSixthBranch.v ((645678727:ℝ)/168755200)/ClassicalSixthBranch.r = (98777408857281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2764
  · change upperPayment 2765 ≤ upperValue ((point split endpoint 4096 2765+point split endpoint 4096 2766)/2)
    have hp : upperPayment 2765 = (190513332048:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2765+point split endpoint 4096 2766)/2 = (645703877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645703877:ℝ)/168755200)*ClassicalSixthBranch.v ((645703877:ℝ)/168755200)/ClassicalSixthBranch.r = (98756988099497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2765
  · change upperPayment 2766 ≤ upperValue ((point split endpoint 4096 2766+point split endpoint 4096 2767)/2)
    have hp : upperPayment 2766 = (190393045698:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2766+point split endpoint 4096 2767)/2 = (645729027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645729027:ℝ)/168755200)*ClassicalSixthBranch.v ((645729027:ℝ)/168755200)/ClassicalSixthBranch.r = (98736569365785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2766
  · change upperPayment 2767 ≤ upperValue ((point split endpoint 4096 2767+point split endpoint 4096 2768)/2)
    have hp : upperPayment 2767 = (190272728485:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2767+point split endpoint 4096 2768)/2 = (645754177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645754177:ℝ)/168755200)*ClassicalSixthBranch.v ((645754177:ℝ)/168755200)/ClassicalSixthBranch.r = (98716152656145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2767
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_172
