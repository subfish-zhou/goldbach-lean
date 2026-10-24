import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints102
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_102 (j : Fin 16) : lowerPayment (16*102+j.val) ≤
    lowerValue ((point 2 split 4096 (16*102+j.val)+point 2 split 4096 (16*102+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1632 ≤ lowerValue ((point 2 split 4096 1632+point 2 split 4096 1633)/2)
    have hp : lowerPayment 1632 = (198363987341:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1632+point 2 split 4096 1633)/2 = (86524623:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86524623:ℝ)/33751040)/ClassicalSixthBranch.v ((86524623:ℝ)/33751040) = (687800603899:ℝ)/342205582488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1632
  · change lowerPayment 1633 ≤ lowerValue ((point 2 split 4096 1633+point 2 split 4096 1634)/2)
    have hp : lowerPayment 1633 = (198459992608:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1633+point 2 split 4096 1634)/2 = (432681377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432681377:ℝ)/168755200)/ClassicalSixthBranch.v ((432681377:ℝ)/168755200) = (27508931609:ℝ)/13686302984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1633
  · change lowerPayment 1634 ≤ lowerValue ((point 2 split 4096 1634+point 2 split 4096 1635)/2)
    have hp : lowerPayment 1634 = (198555981042:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1634+point 2 split 4096 1635)/2 = (432739639:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432739639:ℝ)/168755200)/ClassicalSixthBranch.v ((432739639:ℝ)/168755200) = (687645976551:ℝ)/342109566712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1634
  · change lowerPayment 1635 ≤ lowerValue ((point 2 split 4096 1635+point 2 split 4096 1636)/2)
    have hp : lowerPayment 1635 = (198651952663:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1635+point 2 split 4096 1636)/2 = (432797901:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432797901:ℝ)/168755200)/ClassicalSixthBranch.v ((432797901:ℝ)/168755200) = (687568662877:ℝ)/342061558824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1635
  · change lowerPayment 1636 ≤ lowerValue ((point 2 split 4096 1636+point 2 split 4096 1637)/2)
    have hp : lowerPayment 1636 = (198747907492:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1636+point 2 split 4096 1637)/2 = (432856163:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432856163:ℝ)/168755200)/ClassicalSixthBranch.v ((432856163:ℝ)/168755200) = (687491349203:ℝ)/342013550936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1636
  · change lowerPayment 1637 ≤ lowerValue ((point 2 split 4096 1637+point 2 split 4096 1638)/2)
    have hp : lowerPayment 1637 = (198843845548:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1637+point 2 split 4096 1638)/2 = (17316577:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17316577:ℝ)/6750208)/ClassicalSixthBranch.v ((17316577:ℝ)/6750208) = (687414035529:ℝ)/341965543048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1637
  · change lowerPayment 1638 ≤ lowerValue ((point 2 split 4096 1638+point 2 split 4096 1639)/2)
    have hp : lowerPayment 1638 = (198939766851:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1638+point 2 split 4096 1639)/2 = (432972687:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432972687:ℝ)/168755200)/ClassicalSixthBranch.v ((432972687:ℝ)/168755200) = (137467344371:ℝ)/68383507032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1638
  · change lowerPayment 1639 ≤ lowerValue ((point 2 split 4096 1639+point 2 split 4096 1640)/2)
    have hp : lowerPayment 1639 = (199035671420:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1639+point 2 split 4096 1640)/2 = (433030949:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433030949:ℝ)/168755200)/ClassicalSixthBranch.v ((433030949:ℝ)/168755200) = (687259408181:ℝ)/341869527272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1639
  · change lowerPayment 1640 ≤ lowerValue ((point 2 split 4096 1640+point 2 split 4096 1641)/2)
    have hp : lowerPayment 1640 = (199131559276:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1640+point 2 split 4096 1641)/2 = (433089211:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433089211:ℝ)/168755200)/ClassicalSixthBranch.v ((433089211:ℝ)/168755200) = (687182094507:ℝ)/341821519384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1640
  · change lowerPayment 1641 ≤ lowerValue ((point 2 split 4096 1641+point 2 split 4096 1642)/2)
    have hp : lowerPayment 1641 = (199227430438:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1641+point 2 split 4096 1642)/2 = (433147473:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433147473:ℝ)/168755200)/ClassicalSixthBranch.v ((433147473:ℝ)/168755200) = (687104780833:ℝ)/341773511496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1641
  · change lowerPayment 1642 ≤ lowerValue ((point 2 split 4096 1642+point 2 split 4096 1643)/2)
    have hp : lowerPayment 1642 = (199323284925:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1642+point 2 split 4096 1643)/2 = (86641147:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86641147:ℝ)/33751040)/ClassicalSixthBranch.v ((86641147:ℝ)/33751040) = (687027467159:ℝ)/341725503608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1642
  · change lowerPayment 1643 ≤ lowerValue ((point 2 split 4096 1643+point 2 split 4096 1644)/2)
    have hp : lowerPayment 1643 = (199419122758:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1643+point 2 split 4096 1644)/2 = (433263997:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433263997:ℝ)/168755200)/ClassicalSixthBranch.v ((433263997:ℝ)/168755200) = (137390030697:ℝ)/68335499144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1643
  · change lowerPayment 1644 ≤ lowerValue ((point 2 split 4096 1644+point 2 split 4096 1645)/2)
    have hp : lowerPayment 1644 = (199514943955:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1644+point 2 split 4096 1645)/2 = (433322259:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433322259:ℝ)/168755200)/ClassicalSixthBranch.v ((433322259:ℝ)/168755200) = (686872839811:ℝ)/341629487832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1644
  · change lowerPayment 1645 ≤ lowerValue ((point 2 split 4096 1645+point 2 split 4096 1646)/2)
    have hp : lowerPayment 1645 = (199610748538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1645+point 2 split 4096 1646)/2 = (433380521:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433380521:ℝ)/168755200)/ClassicalSixthBranch.v ((433380521:ℝ)/168755200) = (686795526137:ℝ)/341581479944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1645
  · change lowerPayment 1646 ≤ lowerValue ((point 2 split 4096 1646+point 2 split 4096 1647)/2)
    have hp : lowerPayment 1646 = (199706536525:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1646+point 2 split 4096 1647)/2 = (433438783:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((433438783:ℝ)/168755200)/ClassicalSixthBranch.v ((433438783:ℝ)/168755200) = (686718212463:ℝ)/341533472056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1646
  · change lowerPayment 1647 ≤ lowerValue ((point 2 split 4096 1647+point 2 split 4096 1648)/2)
    have hp : lowerPayment 1647 = (199802307936:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1647+point 2 split 4096 1648)/2 = (86699409:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86699409:ℝ)/33751040)/ClassicalSixthBranch.v ((86699409:ℝ)/33751040) = (686640898789:ℝ)/341485464168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1647
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_102
