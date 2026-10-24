import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints104
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_104 (j : Fin 16) : upperPayment (16*104+j.val) ≤
    upperValue ((point split endpoint 4096 (16*104+j.val)+point split endpoint 4096 (16*104+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1664 ≤ upperValue ((point split endpoint 4096 1664+point split endpoint 4096 1665)/2)
    have hp : upperPayment 1664 = (305636363094:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1664+point split endpoint 4096 1665)/2 = (618013727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618013727:ℝ)/168755200)*ClassicalSixthBranch.v ((618013727:ℝ)/168755200)/ClassicalSixthBranch.r = (122465919219281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1664
  · change upperPayment 1665 ≤ upperValue ((point split endpoint 4096 1665+point split endpoint 4096 1666)/2)
    have hp : upperPayment 1665 = (305546351946:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1665+point split endpoint 4096 1666)/2 = (618038877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618038877:ℝ)/168755200)*ClassicalSixthBranch.v ((618038877:ℝ)/168755200)/ClassicalSixthBranch.r = (122443271982297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1665
  · change upperPayment 1666 ≤ upperValue ((point split endpoint 4096 1666+point split endpoint 4096 1667)/2)
    have hp : upperPayment 1666 = (305456316198:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1666+point split endpoint 4096 1667)/2 = (618064027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618064027:ℝ)/168755200)*ClassicalSixthBranch.v ((618064027:ℝ)/168755200)/ClassicalSixthBranch.r = (122420626769385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1666
  · change upperPayment 1667 ≤ upperValue ((point split endpoint 4096 1667+point split endpoint 4096 1668)/2)
    have hp : upperPayment 1667 = (305366255847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1667+point split endpoint 4096 1668)/2 = (618089177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618089177:ℝ)/168755200)*ClassicalSixthBranch.v ((618089177:ℝ)/168755200)/ClassicalSixthBranch.r = (122397983580545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1667
  · change upperPayment 1668 ≤ upperValue ((point split endpoint 4096 1668+point split endpoint 4096 1669)/2)
    have hp : upperPayment 1668 = (305276170887:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1668+point split endpoint 4096 1669)/2 = (618114327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618114327:ℝ)/168755200)*ClassicalSixthBranch.v ((618114327:ℝ)/168755200)/ClassicalSixthBranch.r = (122375342415777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1668
  · change upperPayment 1669 ≤ upperValue ((point split endpoint 4096 1669+point split endpoint 4096 1670)/2)
    have hp : upperPayment 1669 = (305186061314:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1669+point split endpoint 4096 1670)/2 = (618139477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618139477:ℝ)/168755200)*ClassicalSixthBranch.v ((618139477:ℝ)/168755200)/ClassicalSixthBranch.r = (122352703275081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1669
  · change upperPayment 1670 ≤ upperValue ((point split endpoint 4096 1670+point split endpoint 4096 1671)/2)
    have hp : upperPayment 1670 = (305095927123:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1670+point split endpoint 4096 1671)/2 = (618164627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618164627:ℝ)/168755200)*ClassicalSixthBranch.v ((618164627:ℝ)/168755200)/ClassicalSixthBranch.r = (122330066158457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1670
  · change upperPayment 1671 ≤ upperValue ((point split endpoint 4096 1671+point split endpoint 4096 1672)/2)
    have hp : upperPayment 1671 = (305005768309:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1671+point split endpoint 4096 1672)/2 = (618189777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618189777:ℝ)/168755200)*ClassicalSixthBranch.v ((618189777:ℝ)/168755200)/ClassicalSixthBranch.r = (122307431065905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1671
  · change upperPayment 1672 ≤ upperValue ((point split endpoint 4096 1672+point split endpoint 4096 1673)/2)
    have hp : upperPayment 1672 = (304915584870:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1672+point split endpoint 4096 1673)/2 = (618214927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618214927:ℝ)/168755200)*ClassicalSixthBranch.v ((618214927:ℝ)/168755200)/ClassicalSixthBranch.r = (122284797997425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1672
  · change upperPayment 1673 ≤ upperValue ((point split endpoint 4096 1673+point split endpoint 4096 1674)/2)
    have hp : upperPayment 1673 = (304825376798:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1673+point split endpoint 4096 1674)/2 = (618240077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618240077:ℝ)/168755200)*ClassicalSixthBranch.v ((618240077:ℝ)/168755200)/ClassicalSixthBranch.r = (122262166953017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1673
  · change upperPayment 1674 ≤ upperValue ((point split endpoint 4096 1674+point split endpoint 4096 1675)/2)
    have hp : upperPayment 1674 = (304735144091:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1674+point split endpoint 4096 1675)/2 = (618265227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618265227:ℝ)/168755200)*ClassicalSixthBranch.v ((618265227:ℝ)/168755200)/ClassicalSixthBranch.r = (122239537932681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1674
  · change upperPayment 1675 ≤ upperValue ((point split endpoint 4096 1675+point split endpoint 4096 1676)/2)
    have hp : upperPayment 1675 = (304644886744:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1675+point split endpoint 4096 1676)/2 = (618290377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618290377:ℝ)/168755200)*ClassicalSixthBranch.v ((618290377:ℝ)/168755200)/ClassicalSixthBranch.r = (1186571950839:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1675
  · change upperPayment 1676 ≤ upperValue ((point split endpoint 4096 1676+point split endpoint 4096 1677)/2)
    have hp : upperPayment 1676 = (304554604752:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1676+point split endpoint 4096 1677)/2 = (618315527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618315527:ℝ)/168755200)*ClassicalSixthBranch.v ((618315527:ℝ)/168755200)/ClassicalSixthBranch.r = (122194285964225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1676
  · change upperPayment 1677 ≤ upperValue ((point split endpoint 4096 1677+point split endpoint 4096 1678)/2)
    have hp : upperPayment 1677 = (304464298110:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1677+point split endpoint 4096 1678)/2 = (618340677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618340677:ℝ)/168755200)*ClassicalSixthBranch.v ((618340677:ℝ)/168755200)/ClassicalSixthBranch.r = (122171663016105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1677
  · change upperPayment 1678 ≤ upperValue ((point split endpoint 4096 1678+point split endpoint 4096 1679)/2)
    have hp : upperPayment 1678 = (304373966815:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1678+point split endpoint 4096 1679)/2 = (618365827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618365827:ℝ)/168755200)*ClassicalSixthBranch.v ((618365827:ℝ)/168755200)/ClassicalSixthBranch.r = (122149042092057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1678
  · change upperPayment 1679 ≤ upperValue ((point split endpoint 4096 1679+point split endpoint 4096 1680)/2)
    have hp : upperPayment 1679 = (304283610861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1679+point split endpoint 4096 1680)/2 = (618390977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618390977:ℝ)/168755200)*ClassicalSixthBranch.v ((618390977:ℝ)/168755200)/ClassicalSixthBranch.r = (122126423192081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1679
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_104
