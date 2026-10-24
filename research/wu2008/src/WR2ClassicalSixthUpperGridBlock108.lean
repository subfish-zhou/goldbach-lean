import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints108
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_108 (j : Fin 16) : upperPayment (16*108+j.val) ≤
    upperValue ((point split endpoint 4096 (16*108+j.val)+point split endpoint 4096 (16*108+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1728 ≤ upperValue ((point split endpoint 4096 1728+point split endpoint 4096 1729)/2)
    have hp : upperPayment 1728 = (299825867444:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1728+point split endpoint 4096 1729)/2 = (619623327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619623327:ℝ)/168755200)*ClassicalSixthBranch.v ((619623327:ℝ)/168755200)/ClassicalSixthBranch.r = (121020576581457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1728
  · change upperPayment 1729 ≤ upperValue ((point split endpoint 4096 1729+point split endpoint 4096 1730)/2)
    have hp : upperPayment 1729 = (299734272738:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1729+point split endpoint 4096 1730)/2 = (619648477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619648477:ℝ)/168755200)*ClassicalSixthBranch.v ((619648477:ℝ)/168755200)/ClassicalSixthBranch.r = (120998058885081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1729
  · change upperPayment 1730 ≤ upperValue ((point split endpoint 4096 1730+point split endpoint 4096 1731)/2)
    have hp : upperPayment 1730 = (299642653138:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1730+point split endpoint 4096 1731)/2 = (619673627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619673627:ℝ)/168755200)*ClassicalSixthBranch.v ((619673627:ℝ)/168755200)/ClassicalSixthBranch.r = (120975543212777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1730
  · change upperPayment 1731 ≤ upperValue ((point split endpoint 4096 1731+point split endpoint 4096 1732)/2)
    have hp : upperPayment 1731 = (299551008642:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1731+point split endpoint 4096 1732)/2 = (619698777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619698777:ℝ)/168755200)*ClassicalSixthBranch.v ((619698777:ℝ)/168755200)/ClassicalSixthBranch.r = (120953029564545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1731
  · change upperPayment 1732 ≤ upperValue ((point split endpoint 4096 1732+point split endpoint 4096 1733)/2)
    have hp : upperPayment 1732 = (299459339243:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1732+point split endpoint 4096 1733)/2 = (619723927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619723927:ℝ)/168755200)*ClassicalSixthBranch.v ((619723927:ℝ)/168755200)/ClassicalSixthBranch.r = (120930517940385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1732
  · change upperPayment 1733 ≤ upperValue ((point split endpoint 4096 1733+point split endpoint 4096 1734)/2)
    have hp : upperPayment 1733 = (299367644939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1733+point split endpoint 4096 1734)/2 = (619749077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619749077:ℝ)/168755200)*ClassicalSixthBranch.v ((619749077:ℝ)/168755200)/ClassicalSixthBranch.r = (120908008340297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1733
  · change upperPayment 1734 ≤ upperValue ((point split endpoint 4096 1734+point split endpoint 4096 1735)/2)
    have hp : upperPayment 1734 = (299275925723:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1734+point split endpoint 4096 1735)/2 = (619774227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619774227:ℝ)/168755200)*ClassicalSixthBranch.v ((619774227:ℝ)/168755200)/ClassicalSixthBranch.r = (120885500764281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1734
  · change upperPayment 1735 ≤ upperValue ((point split endpoint 4096 1735+point split endpoint 4096 1736)/2)
    have hp : upperPayment 1735 = (299184181592:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1735+point split endpoint 4096 1736)/2 = (619799377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619799377:ℝ)/168755200)*ClassicalSixthBranch.v ((619799377:ℝ)/168755200)/ClassicalSixthBranch.r = (120862995212337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1735
  · change upperPayment 1736 ≤ upperValue ((point split endpoint 4096 1736+point split endpoint 4096 1737)/2)
    have hp : upperPayment 1736 = (299092412540:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1736+point split endpoint 4096 1737)/2 = (619824527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619824527:ℝ)/168755200)*ClassicalSixthBranch.v ((619824527:ℝ)/168755200)/ClassicalSixthBranch.r = (120840491684465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1736
  · change upperPayment 1737 ≤ upperValue ((point split endpoint 4096 1737+point split endpoint 4096 1738)/2)
    have hp : upperPayment 1737 = (299000618564:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1737+point split endpoint 4096 1738)/2 = (619849677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619849677:ℝ)/168755200)*ClassicalSixthBranch.v ((619849677:ℝ)/168755200)/ClassicalSixthBranch.r = (120817990180665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1737
  · change upperPayment 1738 ≤ upperValue ((point split endpoint 4096 1738+point split endpoint 4096 1739)/2)
    have hp : upperPayment 1738 = (298908799657:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1738+point split endpoint 4096 1739)/2 = (619874827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619874827:ℝ)/168755200)*ClassicalSixthBranch.v ((619874827:ℝ)/168755200)/ClassicalSixthBranch.r = (120795490700937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1738
  · change upperPayment 1739 ≤ upperValue ((point split endpoint 4096 1739+point split endpoint 4096 1740)/2)
    have hp : upperPayment 1739 = (298816955817:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1739+point split endpoint 4096 1740)/2 = (619899977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619899977:ℝ)/168755200)*ClassicalSixthBranch.v ((619899977:ℝ)/168755200)/ClassicalSixthBranch.r = (120772993245281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1739
  · change upperPayment 1740 ≤ upperValue ((point split endpoint 4096 1740+point split endpoint 4096 1741)/2)
    have hp : upperPayment 1740 = (298725087037:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1740+point split endpoint 4096 1741)/2 = (619925127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619925127:ℝ)/168755200)*ClassicalSixthBranch.v ((619925127:ℝ)/168755200)/ClassicalSixthBranch.r = (120750497813697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1740
  · change upperPayment 1741 ≤ upperValue ((point split endpoint 4096 1741+point split endpoint 4096 1742)/2)
    have hp : upperPayment 1741 = (298633193314:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1741+point split endpoint 4096 1742)/2 = (619950277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619950277:ℝ)/168755200)*ClassicalSixthBranch.v ((619950277:ℝ)/168755200)/ClassicalSixthBranch.r = (120728004406185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1741
  · change upperPayment 1742 ≤ upperValue ((point split endpoint 4096 1742+point split endpoint 4096 1743)/2)
    have hp : upperPayment 1742 = (298541274643:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1742+point split endpoint 4096 1743)/2 = (619975427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619975427:ℝ)/168755200)*ClassicalSixthBranch.v ((619975427:ℝ)/168755200)/ClassicalSixthBranch.r = (120705513022745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1742
  · change upperPayment 1743 ≤ upperValue ((point split endpoint 4096 1743+point split endpoint 4096 1744)/2)
    have hp : upperPayment 1743 = (298449331019:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1743+point split endpoint 4096 1744)/2 = (620000577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((620000577:ℝ)/168755200)*ClassicalSixthBranch.v ((620000577:ℝ)/168755200)/ClassicalSixthBranch.r = (120683023663377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1743
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_108
