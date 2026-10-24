import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints103
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_103 (j : Fin 16) : upperPayment (16*103+j.val) ≤
    upperValue ((point split endpoint 4096 (16*103+j.val)+point split endpoint 4096 (16*103+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1648 ≤ upperValue ((point split endpoint 4096 1648+point split endpoint 4096 1649)/2)
    have hp : upperPayment 1648 = (307073199590:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1648+point split endpoint 4096 1649)/2 = (617611327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617611327:ℝ)/168755200)*ClassicalSixthBranch.v ((617611327:ℝ)/168755200)/ClassicalSixthBranch.r = (122828550284817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1648
  · change upperPayment 1649 ≤ upperValue ((point split endpoint 4096 1649+point split endpoint 4096 1650)/2)
    have hp : upperPayment 1649 = (306983581423:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1649+point split endpoint 4096 1650)/2 = (617636477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617636477:ℝ)/168755200)*ClassicalSixthBranch.v ((617636477:ℝ)/168755200)/ClassicalSixthBranch.r = (122805870662681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1649
  · change upperPayment 1650 ≤ upperValue ((point split endpoint 4096 1650+point split endpoint 4096 1651)/2)
    have hp : upperPayment 1650 = (306893938729:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1650+point split endpoint 4096 1651)/2 = (617661627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617661627:ℝ)/168755200)*ClassicalSixthBranch.v ((617661627:ℝ)/168755200)/ClassicalSixthBranch.r = (122783193064617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1650
  · change upperPayment 1651 ≤ upperValue ((point split endpoint 4096 1651+point split endpoint 4096 1652)/2)
    have hp : upperPayment 1651 = (306804271502:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1651+point split endpoint 4096 1652)/2 = (5996959:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5996959:ℝ)/1638400)*ClassicalSixthBranch.v ((5996959:ℝ)/1638400)/ClassicalSixthBranch.r = (1191849684375:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1651
  · change upperPayment 1652 ≤ upperValue ((point split endpoint 4096 1652+point split endpoint 4096 1653)/2)
    have hp : upperPayment 1652 = (306714579739:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1652+point split endpoint 4096 1653)/2 = (617711927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617711927:ℝ)/168755200)*ClassicalSixthBranch.v ((617711927:ℝ)/168755200)/ClassicalSixthBranch.r = (122737843940705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1652
  · change upperPayment 1653 ≤ upperValue ((point split endpoint 4096 1653+point split endpoint 4096 1654)/2)
    have hp : upperPayment 1653 = (306624863435:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1653+point split endpoint 4096 1654)/2 = (617737077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617737077:ℝ)/168755200)*ClassicalSixthBranch.v ((617737077:ℝ)/168755200)/ClassicalSixthBranch.r = (122715172414857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1653
  · change upperPayment 1654 ≤ upperValue ((point split endpoint 4096 1654+point split endpoint 4096 1655)/2)
    have hp : upperPayment 1654 = (306535122585:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1654+point split endpoint 4096 1655)/2 = (617762227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617762227:ℝ)/168755200)*ClassicalSixthBranch.v ((617762227:ℝ)/168755200)/ClassicalSixthBranch.r = (122692502913081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1654
  · change upperPayment 1655 ≤ upperValue ((point split endpoint 4096 1655+point split endpoint 4096 1656)/2)
    have hp : upperPayment 1655 = (306445357185:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1655+point split endpoint 4096 1656)/2 = (617787377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617787377:ℝ)/168755200)*ClassicalSixthBranch.v ((617787377:ℝ)/168755200)/ClassicalSixthBranch.r = (122669835435377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1655
  · change upperPayment 1656 ≤ upperValue ((point split endpoint 4096 1656+point split endpoint 4096 1657)/2)
    have hp : upperPayment 1656 = (306355567231:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1656+point split endpoint 4096 1657)/2 = (617812527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617812527:ℝ)/168755200)*ClassicalSixthBranch.v ((617812527:ℝ)/168755200)/ClassicalSixthBranch.r = (122647169981745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1656
  · change upperPayment 1657 ≤ upperValue ((point split endpoint 4096 1657+point split endpoint 4096 1658)/2)
    have hp : upperPayment 1657 = (306265752718:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1657+point split endpoint 4096 1658)/2 = (617837677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617837677:ℝ)/168755200)*ClassicalSixthBranch.v ((617837677:ℝ)/168755200)/ClassicalSixthBranch.r = (122624506552185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1657
  · change upperPayment 1658 ≤ upperValue ((point split endpoint 4096 1658+point split endpoint 4096 1659)/2)
    have hp : upperPayment 1658 = (306175913641:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1658+point split endpoint 4096 1659)/2 = (617862827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617862827:ℝ)/168755200)*ClassicalSixthBranch.v ((617862827:ℝ)/168755200)/ClassicalSixthBranch.r = (122601845146697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1658
  · change upperPayment 1659 ≤ upperValue ((point split endpoint 4096 1659+point split endpoint 4096 1660)/2)
    have hp : upperPayment 1659 = (306086049996:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1659+point split endpoint 4096 1660)/2 = (617887977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617887977:ℝ)/168755200)*ClassicalSixthBranch.v ((617887977:ℝ)/168755200)/ClassicalSixthBranch.r = (122579185765281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1659
  · change upperPayment 1660 ≤ upperValue ((point split endpoint 4096 1660+point split endpoint 4096 1661)/2)
    have hp : upperPayment 1660 = (305996161779:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1660+point split endpoint 4096 1661)/2 = (617913127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617913127:ℝ)/168755200)*ClassicalSixthBranch.v ((617913127:ℝ)/168755200)/ClassicalSixthBranch.r = (122556528407937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1660
  · change upperPayment 1661 ≤ upperValue ((point split endpoint 4096 1661+point split endpoint 4096 1662)/2)
    have hp : upperPayment 1661 = (305906248984:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1661+point split endpoint 4096 1662)/2 = (617938277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617938277:ℝ)/168755200)*ClassicalSixthBranch.v ((617938277:ℝ)/168755200)/ClassicalSixthBranch.r = (122533873074665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1661
  · change upperPayment 1662 ≤ upperValue ((point split endpoint 4096 1662+point split endpoint 4096 1663)/2)
    have hp : upperPayment 1662 = (305816311608:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1662+point split endpoint 4096 1663)/2 = (617963427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617963427:ℝ)/168755200)*ClassicalSixthBranch.v ((617963427:ℝ)/168755200)/ClassicalSixthBranch.r = (122511219765465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1662
  · change upperPayment 1663 ≤ upperValue ((point split endpoint 4096 1663+point split endpoint 4096 1664)/2)
    have hp : upperPayment 1663 = (305726349646:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1663+point split endpoint 4096 1664)/2 = (617988577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617988577:ℝ)/168755200)*ClassicalSixthBranch.v ((617988577:ℝ)/168755200)/ClassicalSixthBranch.r = (122488568480337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1663
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_103
