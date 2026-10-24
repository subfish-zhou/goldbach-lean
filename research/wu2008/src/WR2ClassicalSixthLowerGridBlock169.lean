import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints169
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_169 (j : Fin 16) : lowerPayment (16*169+j.val) ≤
    lowerValue ((point 2 split 4096 (16*169+j.val)+point 2 split 4096 (16*169+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2704 ≤ lowerValue ((point 2 split 4096 2704+point 2 split 4096 2705)/2)
    have hp : lowerPayment 2704 = (295224846702:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2704+point 2 split 4096 2705)/2 = (495079979:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495079979:ℝ)/168755200)/ClassicalSixthBranch.v ((495079979:ℝ)/168755200) = (604920345371:ℝ)/290741126552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2704
  · change lowerPayment 2705 ≤ lowerValue ((point 2 split 4096 2705+point 2 split 4096 2706)/2)
    have hp : lowerPayment 2705 = (295312607911:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2705+point 2 split 4096 2706)/2 = (495138241:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495138241:ℝ)/168755200)/ClassicalSixthBranch.v ((495138241:ℝ)/168755200) = (604843031697:ℝ)/290693118664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2705
  · change lowerPayment 2706 ≤ lowerValue ((point 2 split 4096 2706+point 2 split 4096 2707)/2)
    have hp : lowerPayment 2706 = (295400369607:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2706+point 2 split 4096 2707)/2 = (495196503:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495196503:ℝ)/168755200)/ClassicalSixthBranch.v ((495196503:ℝ)/168755200) = (604765718023:ℝ)/290645110776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2706
  · change lowerPayment 2707 ≤ lowerValue ((point 2 split 4096 2707+point 2 split 4096 2708)/2)
    have hp : lowerPayment 2707 = (295488131805:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2707+point 2 split 4096 2708)/2 = (99050953:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99050953:ℝ)/33751040)/ClassicalSixthBranch.v ((99050953:ℝ)/33751040) = (604688404349:ℝ)/290597102888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2707
  · change lowerPayment 2708 ≤ lowerValue ((point 2 split 4096 2708+point 2 split 4096 2709)/2)
    have hp : lowerPayment 2708 = (295575894519:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2708+point 2 split 4096 2709)/2 = (495313027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495313027:ℝ)/168755200)/ClassicalSixthBranch.v ((495313027:ℝ)/168755200) = (24184443627:ℝ)/11621963800 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2708
  · change lowerPayment 2709 ≤ lowerValue ((point 2 split 4096 2709+point 2 split 4096 2710)/2)
    have hp : lowerPayment 2709 = (295663657762:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2709+point 2 split 4096 2710)/2 = (495371289:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495371289:ℝ)/168755200)/ClassicalSixthBranch.v ((495371289:ℝ)/168755200) = (604533777001:ℝ)/290501087112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2709
  · change lowerPayment 2710 ≤ lowerValue ((point 2 split 4096 2710+point 2 split 4096 2711)/2)
    have hp : lowerPayment 2710 = (295751421550:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2710+point 2 split 4096 2711)/2 = (495429551:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495429551:ℝ)/168755200)/ClassicalSixthBranch.v ((495429551:ℝ)/168755200) = (604456463327:ℝ)/290453079224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2710
  · change lowerPayment 2711 ≤ lowerValue ((point 2 split 4096 2711+point 2 split 4096 2712)/2)
    have hp : lowerPayment 2711 = (295839185896:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2711+point 2 split 4096 2712)/2 = (495487813:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495487813:ℝ)/168755200)/ClassicalSixthBranch.v ((495487813:ℝ)/168755200) = (604379149653:ℝ)/290405071336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2711
  · change lowerPayment 2712 ≤ lowerValue ((point 2 split 4096 2712+point 2 split 4096 2713)/2)
    have hp : lowerPayment 2712 = (295926950814:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2712+point 2 split 4096 2713)/2 = (19821843:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19821843:ℝ)/6750208)/ClassicalSixthBranch.v ((19821843:ℝ)/6750208) = (604301835979:ℝ)/290357063448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2712
  · change lowerPayment 2713 ≤ lowerValue ((point 2 split 4096 2713+point 2 split 4096 2714)/2)
    have hp : lowerPayment 2713 = (296014716319:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2713+point 2 split 4096 2714)/2 = (495604337:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495604337:ℝ)/168755200)/ClassicalSixthBranch.v ((495604337:ℝ)/168755200) = (120844904461:ℝ)/58061811112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2713
  · change lowerPayment 2714 ≤ lowerValue ((point 2 split 4096 2714+point 2 split 4096 2715)/2)
    have hp : lowerPayment 2714 = (296102482425:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2714+point 2 split 4096 2715)/2 = (495662599:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495662599:ℝ)/168755200)/ClassicalSixthBranch.v ((495662599:ℝ)/168755200) = (604147208631:ℝ)/290261047672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2714
  · change lowerPayment 2715 ≤ lowerValue ((point 2 split 4096 2715+point 2 split 4096 2716)/2)
    have hp : lowerPayment 2715 = (296190249146:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2715+point 2 split 4096 2716)/2 = (495720861:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495720861:ℝ)/168755200)/ClassicalSixthBranch.v ((495720861:ℝ)/168755200) = (604069894957:ℝ)/290213039784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2715
  · change lowerPayment 2716 ≤ lowerValue ((point 2 split 4096 2716+point 2 split 4096 2717)/2)
    have hp : lowerPayment 2716 = (296278016496:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2716+point 2 split 4096 2717)/2 = (495779123:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495779123:ℝ)/168755200)/ClassicalSixthBranch.v ((495779123:ℝ)/168755200) = (603992581283:ℝ)/290165031896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2716
  · change lowerPayment 2717 ≤ lowerValue ((point 2 split 4096 2717+point 2 split 4096 2718)/2)
    have hp : lowerPayment 2717 = (296365784489:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2717+point 2 split 4096 2718)/2 = (99167477:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99167477:ℝ)/33751040)/ClassicalSixthBranch.v ((99167477:ℝ)/33751040) = (603915267609:ℝ)/290117024008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2717
  · change lowerPayment 2718 ≤ lowerValue ((point 2 split 4096 2718+point 2 split 4096 2719)/2)
    have hp : lowerPayment 2718 = (296453553140:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2718+point 2 split 4096 2719)/2 = (495895647:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495895647:ℝ)/168755200)/ClassicalSixthBranch.v ((495895647:ℝ)/168755200) = (120767590787:ℝ)/58013803224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2718
  · change lowerPayment 2719 ≤ lowerValue ((point 2 split 4096 2719+point 2 split 4096 2720)/2)
    have hp : lowerPayment 2719 = (296541322463:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2719+point 2 split 4096 2720)/2 = (495953909:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495953909:ℝ)/168755200)/ClassicalSixthBranch.v ((495953909:ℝ)/168755200) = (603760640261:ℝ)/290021008232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2719
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_169
