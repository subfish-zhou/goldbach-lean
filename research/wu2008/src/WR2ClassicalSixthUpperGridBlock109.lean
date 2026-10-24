import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints109
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_109 (j : Fin 16) : upperPayment (16*109+j.val) ≤
    upperValue ((point split endpoint 4096 (16*109+j.val)+point split endpoint 4096 (16*109+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1744 ≤ upperValue ((point split endpoint 4096 1744+point split endpoint 4096 1745)/2)
    have hp : upperPayment 1744 = (298357362437:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1744+point split endpoint 4096 1745)/2 = (620025727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620025727:ℝ)/168755200)*ClassicalSixthBranch.v ((620025727:ℝ)/168755200)/ClassicalSixthBranch.r = (120660536328081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1744
  · change upperPayment 1745 ≤ upperValue ((point split endpoint 4096 1745+point split endpoint 4096 1746)/2)
    have hp : upperPayment 1745 = (298265368893:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1745+point split endpoint 4096 1746)/2 = (620050877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620050877:ℝ)/168755200)*ClassicalSixthBranch.v ((620050877:ℝ)/168755200)/ClassicalSixthBranch.r = (120638051016857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1745
  · change upperPayment 1746 ≤ upperValue ((point split endpoint 4096 1746+point split endpoint 4096 1747)/2)
    have hp : upperPayment 1746 = (298173350382:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1746+point split endpoint 4096 1747)/2 = (620076027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620076027:ℝ)/168755200)*ClassicalSixthBranch.v ((620076027:ℝ)/168755200)/ClassicalSixthBranch.r = (120615567729705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1746
  · change upperPayment 1747 ≤ upperValue ((point split endpoint 4096 1747+point split endpoint 4096 1748)/2)
    have hp : upperPayment 1747 = (298081306900:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1747+point split endpoint 4096 1748)/2 = (620101177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620101177:ℝ)/168755200)*ClassicalSixthBranch.v ((620101177:ℝ)/168755200)/ClassicalSixthBranch.r = (120593086466625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1747
  · change upperPayment 1748 ≤ upperValue ((point split endpoint 4096 1748+point split endpoint 4096 1749)/2)
    have hp : upperPayment 1748 = (297989238441:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1748+point split endpoint 4096 1749)/2 = (620126327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620126327:ℝ)/168755200)*ClassicalSixthBranch.v ((620126327:ℝ)/168755200)/ClassicalSixthBranch.r = (120570607227617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1748
  · change upperPayment 1749 ≤ upperValue ((point split endpoint 4096 1749+point split endpoint 4096 1750)/2)
    have hp : upperPayment 1749 = (297897145002:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1749+point split endpoint 4096 1750)/2 = (620151477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620151477:ℝ)/168755200)*ClassicalSixthBranch.v ((620151477:ℝ)/168755200)/ClassicalSixthBranch.r = (120548130012681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1749
  · change upperPayment 1750 ≤ upperValue ((point split endpoint 4096 1750+point split endpoint 4096 1751)/2)
    have hp : upperPayment 1750 = (297805026576:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1750+point split endpoint 4096 1751)/2 = (620176627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620176627:ℝ)/168755200)*ClassicalSixthBranch.v ((620176627:ℝ)/168755200)/ClassicalSixthBranch.r = (120525654821817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1750
  · change upperPayment 1751 ≤ upperValue ((point split endpoint 4096 1751+point split endpoint 4096 1752)/2)
    have hp : upperPayment 1751 = (297712883161:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1751+point split endpoint 4096 1752)/2 = (620201777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620201777:ℝ)/168755200)*ClassicalSixthBranch.v ((620201777:ℝ)/168755200)/ClassicalSixthBranch.r = (120503181655025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1751
  · change upperPayment 1752 ≤ upperValue ((point split endpoint 4096 1752+point split endpoint 4096 1753)/2)
    have hp : upperPayment 1752 = (297620714751:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1752+point split endpoint 4096 1753)/2 = (620226927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620226927:ℝ)/168755200)*ClassicalSixthBranch.v ((620226927:ℝ)/168755200)/ClassicalSixthBranch.r = (120480710512305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1752
  · change upperPayment 1753 ≤ upperValue ((point split endpoint 4096 1753+point split endpoint 4096 1754)/2)
    have hp : upperPayment 1753 = (297528521341:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1753+point split endpoint 4096 1754)/2 = (620252077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620252077:ℝ)/168755200)*ClassicalSixthBranch.v ((620252077:ℝ)/168755200)/ClassicalSixthBranch.r = (120458241393657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1753
  · change upperPayment 1754 ≤ upperValue ((point split endpoint 4096 1754+point split endpoint 4096 1755)/2)
    have hp : upperPayment 1754 = (297436302927:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1754+point split endpoint 4096 1755)/2 = (6022109:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6022109:ℝ)/1638400)*ClassicalSixthBranch.v ((6022109:ℝ)/1638400)/ClassicalSixthBranch.r = (1169279362127:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1754
  · change upperPayment 1755 ≤ upperValue ((point split endpoint 4096 1755+point split endpoint 4096 1756)/2)
    have hp : upperPayment 1755 = (297344059503:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1755+point split endpoint 4096 1756)/2 = (620302377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620302377:ℝ)/168755200)*ClassicalSixthBranch.v ((620302377:ℝ)/168755200)/ClassicalSixthBranch.r = (120413309228577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1755
  · change upperPayment 1756 ≤ upperValue ((point split endpoint 4096 1756+point split endpoint 4096 1757)/2)
    have hp : upperPayment 1756 = (297251791067:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1756+point split endpoint 4096 1757)/2 = (620327527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620327527:ℝ)/168755200)*ClassicalSixthBranch.v ((620327527:ℝ)/168755200)/ClassicalSixthBranch.r = (120390846182145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1756
  · change upperPayment 1757 ≤ upperValue ((point split endpoint 4096 1757+point split endpoint 4096 1758)/2)
    have hp : upperPayment 1757 = (297159497611:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1757+point split endpoint 4096 1758)/2 = (620352677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620352677:ℝ)/168755200)*ClassicalSixthBranch.v ((620352677:ℝ)/168755200)/ClassicalSixthBranch.r = (120368385159785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1757
  · change upperPayment 1758 ≤ upperValue ((point split endpoint 4096 1758+point split endpoint 4096 1759)/2)
    have hp : upperPayment 1758 = (297067179133:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1758+point split endpoint 4096 1759)/2 = (620377827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620377827:ℝ)/168755200)*ClassicalSixthBranch.v ((620377827:ℝ)/168755200)/ClassicalSixthBranch.r = (120345926161497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1758
  · change upperPayment 1759 ≤ upperValue ((point split endpoint 4096 1759+point split endpoint 4096 1760)/2)
    have hp : upperPayment 1759 = (296974835627:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1759+point split endpoint 4096 1760)/2 = (620402977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620402977:ℝ)/168755200)*ClassicalSixthBranch.v ((620402977:ℝ)/168755200)/ClassicalSixthBranch.r = (120323469187281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1759
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_109
