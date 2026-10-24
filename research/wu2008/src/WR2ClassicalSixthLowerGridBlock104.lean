import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints104
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_104 (j : Fin 16) : lowerPayment (16*104+j.val) ≤
    lowerValue ((point 2 split 4096 (16*104+j.val)+point 2 split 4096 (16*104+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1664 ≤ lowerValue ((point 2 split 4096 1664+point 2 split 4096 1665)/2)
    have hp : lowerPayment 1664 = (201427904791:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1664+point 2 split 4096 1665)/2 = (434487499:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434487499:ℝ)/168755200)/ClassicalSixthBranch.v ((434487499:ℝ)/168755200) = (685326566331:ℝ)/340669330072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1664
  · change lowerPayment 1665 ≤ lowerValue ((point 2 split 4096 1665+point 2 split 4096 1666)/2)
    have hp : lowerPayment 1665 = (201523381183:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1665+point 2 split 4096 1666)/2 = (434545761:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434545761:ℝ)/168755200)/ClassicalSixthBranch.v ((434545761:ℝ)/168755200) = (685249252657:ℝ)/340621322184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1665
  · change lowerPayment 1666 ≤ lowerValue ((point 2 split 4096 1666+point 2 split 4096 1667)/2)
    have hp : lowerPayment 1666 = (201618841370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1666+point 2 split 4096 1667)/2 = (434604023:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434604023:ℝ)/168755200)/ClassicalSixthBranch.v ((434604023:ℝ)/168755200) = (685171938983:ℝ)/340573314296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1666
  · change lowerPayment 1667 ≤ lowerValue ((point 2 split 4096 1667+point 2 split 4096 1668)/2)
    have hp : lowerPayment 1667 = (201714285373:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1667+point 2 split 4096 1668)/2 = (86932457:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86932457:ℝ)/33751040)/ClassicalSixthBranch.v ((86932457:ℝ)/33751040) = (685094625309:ℝ)/340525306408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1667
  · change lowerPayment 1668 ≤ lowerValue ((point 2 split 4096 1668+point 2 split 4096 1669)/2)
    have hp : lowerPayment 1668 = (201809713210:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1668+point 2 split 4096 1669)/2 = (434720547:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434720547:ℝ)/168755200)/ClassicalSixthBranch.v ((434720547:ℝ)/168755200) = (137003462327:ℝ)/68095459704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1668
  · change lowerPayment 1669 ≤ lowerValue ((point 2 split 4096 1669+point 2 split 4096 1670)/2)
    have hp : lowerPayment 1669 = (201905124900:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1669+point 2 split 4096 1670)/2 = (434778809:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434778809:ℝ)/168755200)/ClassicalSixthBranch.v ((434778809:ℝ)/168755200) = (684939997961:ℝ)/340429290632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1669
  · change lowerPayment 1670 ≤ lowerValue ((point 2 split 4096 1670+point 2 split 4096 1671)/2)
    have hp : lowerPayment 1670 = (202000520464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1670+point 2 split 4096 1671)/2 = (434837071:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434837071:ℝ)/168755200)/ClassicalSixthBranch.v ((434837071:ℝ)/168755200) = (684862684287:ℝ)/340381282744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1670
  · change lowerPayment 1671 ≤ lowerValue ((point 2 split 4096 1671+point 2 split 4096 1672)/2)
    have hp : lowerPayment 1671 = (202095899920:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1671+point 2 split 4096 1672)/2 = (434895333:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((434895333:ℝ)/168755200)/ClassicalSixthBranch.v ((434895333:ℝ)/168755200) = (684785370613:ℝ)/340333274856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1671
  · change lowerPayment 1672 ≤ lowerValue ((point 2 split 4096 1672+point 2 split 4096 1673)/2)
    have hp : lowerPayment 1672 = (202191263289:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1672+point 2 split 4096 1673)/2 = (86990719:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86990719:ℝ)/33751040)/ClassicalSixthBranch.v ((86990719:ℝ)/33751040) = (684708056939:ℝ)/340285266968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1672
  · change lowerPayment 1673 ≤ lowerValue ((point 2 split 4096 1673+point 2 split 4096 1674)/2)
    have hp : lowerPayment 1673 = (202286610589:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1673+point 2 split 4096 1674)/2 = (435011857:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435011857:ℝ)/168755200)/ClassicalSixthBranch.v ((435011857:ℝ)/168755200) = (136926148653:ℝ)/68047451816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1673
  · change lowerPayment 1674 ≤ lowerValue ((point 2 split 4096 1674+point 2 split 4096 1675)/2)
    have hp : lowerPayment 1674 = (202381941839:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1674+point 2 split 4096 1675)/2 = (435070119:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435070119:ℝ)/168755200)/ClassicalSixthBranch.v ((435070119:ℝ)/168755200) = (684553429591:ℝ)/340189251192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1674
  · change lowerPayment 1675 ≤ lowerValue ((point 2 split 4096 1675+point 2 split 4096 1676)/2)
    have hp : lowerPayment 1675 = (202477257060:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1675+point 2 split 4096 1676)/2 = (435128381:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435128381:ℝ)/168755200)/ClassicalSixthBranch.v ((435128381:ℝ)/168755200) = (684476115917:ℝ)/340141243304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1675
  · change lowerPayment 1676 ≤ lowerValue ((point 2 split 4096 1676+point 2 split 4096 1677)/2)
    have hp : lowerPayment 1676 = (202572556270:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1676+point 2 split 4096 1677)/2 = (435186643:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435186643:ℝ)/168755200)/ClassicalSixthBranch.v ((435186643:ℝ)/168755200) = (684398802243:ℝ)/340093235416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1676
  · change lowerPayment 1677 ≤ lowerValue ((point 2 split 4096 1677+point 2 split 4096 1678)/2)
    have hp : lowerPayment 1677 = (202667839489:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1677+point 2 split 4096 1678)/2 = (87048981:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87048981:ℝ)/33751040)/ClassicalSixthBranch.v ((87048981:ℝ)/33751040) = (684321488569:ℝ)/340045227528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1677
  · change lowerPayment 1678 ≤ lowerValue ((point 2 split 4096 1678+point 2 split 4096 1679)/2)
    have hp : lowerPayment 1678 = (202763106736:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1678+point 2 split 4096 1679)/2 = (435303167:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435303167:ℝ)/168755200)/ClassicalSixthBranch.v ((435303167:ℝ)/168755200) = (136848834979:ℝ)/67999443928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1678
  · change lowerPayment 1679 ≤ lowerValue ((point 2 split 4096 1679+point 2 split 4096 1680)/2)
    have hp : lowerPayment 1679 = (202858358030:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1679+point 2 split 4096 1680)/2 = (435361429:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435361429:ℝ)/168755200)/ClassicalSixthBranch.v ((435361429:ℝ)/168755200) = (684166861221:ℝ)/339949211752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1679
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_104
