import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints111
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_111 (j : Fin 16) : upperPayment (16*111+j.val) ≤
    upperValue ((point split endpoint 4096 (16*111+j.val)+point split endpoint 4096 (16*111+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1776 ≤ upperValue ((point split endpoint 4096 1776+point split endpoint 4096 1777)/2)
    have hp : upperPayment 1776 = (295401162230:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1776+point split endpoint 4096 1777)/2 = (620830527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620830527:ℝ)/168755200)*ClassicalSixthBranch.v ((620830527:ℝ)/168755200)/ClassicalSixthBranch.r = (119942010308625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1776
  · change upperPayment 1777 ≤ upperValue ((point split endpoint 4096 1777+point split endpoint 4096 1778)/2)
    have hp : upperPayment 1777 = (295308367421:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1777+point split endpoint 4096 1778)/2 = (620855677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620855677:ℝ)/168755200)*ClassicalSixthBranch.v ((620855677:ℝ)/168755200)/ClassicalSixthBranch.r = (119919589767705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1777
  · change upperPayment 1778 ≤ upperValue ((point split endpoint 4096 1778+point split endpoint 4096 1779)/2)
    have hp : upperPayment 1778 = (295215547495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1778+point split endpoint 4096 1779)/2 = (620880827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620880827:ℝ)/168755200)*ClassicalSixthBranch.v ((620880827:ℝ)/168755200)/ClassicalSixthBranch.r = (1164050206319:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1778
  · change upperPayment 1779 ≤ upperValue ((point split endpoint 4096 1779+point split endpoint 4096 1780)/2)
    have hp : upperPayment 1779 = (295122702446:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1779+point split endpoint 4096 1780)/2 = (620905977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620905977:ℝ)/168755200)*ClassicalSixthBranch.v ((620905977:ℝ)/168755200)/ClassicalSixthBranch.r = (119874754758081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1779
  · change upperPayment 1780 ≤ upperValue ((point split endpoint 4096 1780+point split endpoint 4096 1781)/2)
    have hp : upperPayment 1780 = (295029832271:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1780+point split endpoint 4096 1781)/2 = (620931127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620931127:ℝ)/168755200)*ClassicalSixthBranch.v ((620931127:ℝ)/168755200)/ClassicalSixthBranch.r = (119852340289377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1780
  · change upperPayment 1781 ≤ upperValue ((point split endpoint 4096 1781+point split endpoint 4096 1782)/2)
    have hp : upperPayment 1781 = (294936936965:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1781+point split endpoint 4096 1782)/2 = (620956277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620956277:ℝ)/168755200)*ClassicalSixthBranch.v ((620956277:ℝ)/168755200)/ClassicalSixthBranch.r = (119829927844745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1781
  · change upperPayment 1782 ≤ upperValue ((point split endpoint 4096 1782+point split endpoint 4096 1783)/2)
    have hp : upperPayment 1782 = (294844016523:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1782+point split endpoint 4096 1783)/2 = (620981427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620981427:ℝ)/168755200)*ClassicalSixthBranch.v ((620981427:ℝ)/168755200)/ClassicalSixthBranch.r = (119807517424185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1782
  · change upperPayment 1783 ≤ upperValue ((point split endpoint 4096 1783+point split endpoint 4096 1784)/2)
    have hp : upperPayment 1783 = (294751070939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1783+point split endpoint 4096 1784)/2 = (621006577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621006577:ℝ)/168755200)*ClassicalSixthBranch.v ((621006577:ℝ)/168755200)/ClassicalSixthBranch.r = (119785109027697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1783
  · change upperPayment 1784 ≤ upperValue ((point split endpoint 4096 1784+point split endpoint 4096 1785)/2)
    have hp : upperPayment 1784 = (294658100210:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1784+point split endpoint 4096 1785)/2 = (621031727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621031727:ℝ)/168755200)*ClassicalSixthBranch.v ((621031727:ℝ)/168755200)/ClassicalSixthBranch.r = (119762702655281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1784
  · change upperPayment 1785 ≤ upperValue ((point split endpoint 4096 1785+point split endpoint 4096 1786)/2)
    have hp : upperPayment 1785 = (294565104331:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1785+point split endpoint 4096 1786)/2 = (621056877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621056877:ℝ)/168755200)*ClassicalSixthBranch.v ((621056877:ℝ)/168755200)/ClassicalSixthBranch.r = (119740298306937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1785
  · change upperPayment 1786 ≤ upperValue ((point split endpoint 4096 1786+point split endpoint 4096 1787)/2)
    have hp : upperPayment 1786 = (294472083296:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1786+point split endpoint 4096 1787)/2 = (621082027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621082027:ℝ)/168755200)*ClassicalSixthBranch.v ((621082027:ℝ)/168755200)/ClassicalSixthBranch.r = (119717895982665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1786
  · change upperPayment 1787 ≤ upperValue ((point split endpoint 4096 1787+point split endpoint 4096 1788)/2)
    have hp : upperPayment 1787 = (294379037102:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1787+point split endpoint 4096 1788)/2 = (621107177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621107177:ℝ)/168755200)*ClassicalSixthBranch.v ((621107177:ℝ)/168755200)/ClassicalSixthBranch.r = (119695495682465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1787
  · change upperPayment 1788 ≤ upperValue ((point split endpoint 4096 1788+point split endpoint 4096 1789)/2)
    have hp : upperPayment 1788 = (294285965743:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1788+point split endpoint 4096 1789)/2 = (621132327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621132327:ℝ)/168755200)*ClassicalSixthBranch.v ((621132327:ℝ)/168755200)/ClassicalSixthBranch.r = (119673097406337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1788
  · change upperPayment 1789 ≤ upperValue ((point split endpoint 4096 1789+point split endpoint 4096 1790)/2)
    have hp : upperPayment 1789 = (294192869215:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1789+point split endpoint 4096 1790)/2 = (621157477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621157477:ℝ)/168755200)*ClassicalSixthBranch.v ((621157477:ℝ)/168755200)/ClassicalSixthBranch.r = (119650701154281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1789
  · change upperPayment 1790 ≤ upperValue ((point split endpoint 4096 1790+point split endpoint 4096 1791)/2)
    have hp : upperPayment 1790 = (294099747513:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1790+point split endpoint 4096 1791)/2 = (621182627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621182627:ℝ)/168755200)*ClassicalSixthBranch.v ((621182627:ℝ)/168755200)/ClassicalSixthBranch.r = (119628306926297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1790
  · change upperPayment 1791 ≤ upperValue ((point split endpoint 4096 1791+point split endpoint 4096 1792)/2)
    have hp : upperPayment 1791 = (294006600632:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1791+point split endpoint 4096 1792)/2 = (621207777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621207777:ℝ)/168755200)*ClassicalSixthBranch.v ((621207777:ℝ)/168755200)/ClassicalSixthBranch.r = (119605914722385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1791
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_111
