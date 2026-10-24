import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints112
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_112 (j : Fin 16) : upperPayment (16*112+j.val) ≤
    upperValue ((point split endpoint 4096 (16*112+j.val)+point split endpoint 4096 (16*112+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1792 ≤ upperValue ((point split endpoint 4096 1792+point split endpoint 4096 1793)/2)
    have hp : upperPayment 1792 = (293913428567:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1792+point split endpoint 4096 1793)/2 = (621232927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621232927:ℝ)/168755200)*ClassicalSixthBranch.v ((621232927:ℝ)/168755200)/ClassicalSixthBranch.r = (119583524542545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1792
  · change upperPayment 1793 ≤ upperValue ((point split endpoint 4096 1793+point split endpoint 4096 1794)/2)
    have hp : upperPayment 1793 = (293820231314:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1793+point split endpoint 4096 1794)/2 = (621258077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621258077:ℝ)/168755200)*ClassicalSixthBranch.v ((621258077:ℝ)/168755200)/ClassicalSixthBranch.r = (119561136386777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1793
  · change upperPayment 1794 ≤ upperValue ((point split endpoint 4096 1794+point split endpoint 4096 1795)/2)
    have hp : upperPayment 1794 = (293727008868:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1794+point split endpoint 4096 1795)/2 = (621283227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621283227:ℝ)/168755200)*ClassicalSixthBranch.v ((621283227:ℝ)/168755200)/ClassicalSixthBranch.r = (119538750255081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1794
  · change upperPayment 1795 ≤ upperValue ((point split endpoint 4096 1795+point split endpoint 4096 1796)/2)
    have hp : upperPayment 1795 = (293633761224:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1795+point split endpoint 4096 1796)/2 = (621308377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621308377:ℝ)/168755200)*ClassicalSixthBranch.v ((621308377:ℝ)/168755200)/ClassicalSixthBranch.r = (119516366147457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1795
  · change upperPayment 1796 ≤ upperValue ((point split endpoint 4096 1796+point split endpoint 4096 1797)/2)
    have hp : upperPayment 1796 = (293540488378:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1796+point split endpoint 4096 1797)/2 = (621333527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621333527:ℝ)/168755200)*ClassicalSixthBranch.v ((621333527:ℝ)/168755200)/ClassicalSixthBranch.r = (119493984063905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1796
  · change upperPayment 1797 ≤ upperValue ((point split endpoint 4096 1797+point split endpoint 4096 1798)/2)
    have hp : upperPayment 1797 = (293447190324:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1797+point split endpoint 4096 1798)/2 = (621358677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621358677:ℝ)/168755200)*ClassicalSixthBranch.v ((621358677:ℝ)/168755200)/ClassicalSixthBranch.r = (119471604004425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1797
  · change upperPayment 1798 ≤ upperValue ((point split endpoint 4096 1798+point split endpoint 4096 1799)/2)
    have hp : upperPayment 1798 = (293353867058:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1798+point split endpoint 4096 1799)/2 = (621383827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621383827:ℝ)/168755200)*ClassicalSixthBranch.v ((621383827:ℝ)/168755200)/ClassicalSixthBranch.r = (119449225969017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1798
  · change upperPayment 1799 ≤ upperValue ((point split endpoint 4096 1799+point split endpoint 4096 1800)/2)
    have hp : upperPayment 1799 = (293260518574:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1799+point split endpoint 4096 1800)/2 = (621408977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621408977:ℝ)/168755200)*ClassicalSixthBranch.v ((621408977:ℝ)/168755200)/ClassicalSixthBranch.r = (119426849957681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1799
  · change upperPayment 1800 ≤ upperValue ((point split endpoint 4096 1800+point split endpoint 4096 1801)/2)
    have hp : upperPayment 1800 = (293167144870:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1800+point split endpoint 4096 1801)/2 = (621434127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621434127:ℝ)/168755200)*ClassicalSixthBranch.v ((621434127:ℝ)/168755200)/ClassicalSixthBranch.r = (119404475970417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1800
  · change upperPayment 1801 ≤ upperValue ((point split endpoint 4096 1801+point split endpoint 4096 1802)/2)
    have hp : upperPayment 1801 = (293073745939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1801+point split endpoint 4096 1802)/2 = (621459277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621459277:ℝ)/168755200)*ClassicalSixthBranch.v ((621459277:ℝ)/168755200)/ClassicalSixthBranch.r = (119382104007225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1801
  · change upperPayment 1802 ≤ upperValue ((point split endpoint 4096 1802+point split endpoint 4096 1803)/2)
    have hp : upperPayment 1802 = (292980321776:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1802+point split endpoint 4096 1803)/2 = (621484427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621484427:ℝ)/168755200)*ClassicalSixthBranch.v ((621484427:ℝ)/168755200)/ClassicalSixthBranch.r = (119359734068105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1802
  · change upperPayment 1803 ≤ upperValue ((point split endpoint 4096 1803+point split endpoint 4096 1804)/2)
    have hp : upperPayment 1803 = (292886872378:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1803+point split endpoint 4096 1804)/2 = (621509577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621509577:ℝ)/168755200)*ClassicalSixthBranch.v ((621509577:ℝ)/168755200)/ClassicalSixthBranch.r = (119337366153057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1803
  · change upperPayment 1804 ≤ upperValue ((point split endpoint 4096 1804+point split endpoint 4096 1805)/2)
    have hp : upperPayment 1804 = (292793397739:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1804+point split endpoint 4096 1805)/2 = (621534727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621534727:ℝ)/168755200)*ClassicalSixthBranch.v ((621534727:ℝ)/168755200)/ClassicalSixthBranch.r = (119315000262081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1804
  · change upperPayment 1805 ≤ upperValue ((point split endpoint 4096 1805+point split endpoint 4096 1806)/2)
    have hp : upperPayment 1805 = (292699897854:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1805+point split endpoint 4096 1806)/2 = (621559877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621559877:ℝ)/168755200)*ClassicalSixthBranch.v ((621559877:ℝ)/168755200)/ClassicalSixthBranch.r = (119292636395177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1805
  · change upperPayment 1806 ≤ upperValue ((point split endpoint 4096 1806+point split endpoint 4096 1807)/2)
    have hp : upperPayment 1806 = (292606372719:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1806+point split endpoint 4096 1807)/2 = (621585027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621585027:ℝ)/168755200)*ClassicalSixthBranch.v ((621585027:ℝ)/168755200)/ClassicalSixthBranch.r = (119270274552345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1806
  · change upperPayment 1807 ≤ upperValue ((point split endpoint 4096 1807+point split endpoint 4096 1808)/2)
    have hp : upperPayment 1807 = (292512822329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1807+point split endpoint 4096 1808)/2 = (621610177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((621610177:ℝ)/168755200)*ClassicalSixthBranch.v ((621610177:ℝ)/168755200)/ClassicalSixthBranch.r = (119247914733585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1807
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_112
