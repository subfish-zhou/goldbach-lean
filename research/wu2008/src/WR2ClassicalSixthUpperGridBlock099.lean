import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints099
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_099 (j : Fin 16) : upperPayment (16*99+j.val) ≤
    upperValue ((point split endpoint 4096 (16*99+j.val)+point split endpoint 4096 (16*99+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1584 ≤ upperValue ((point split endpoint 4096 1584+point split endpoint 4096 1585)/2)
    have hp : upperPayment 1584 = (312757948862:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1584+point split endpoint 4096 1585)/2 = (616001727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616001727:ℝ)/168755200)*ClassicalSixthBranch.v ((616001727:ℝ)/168755200)/ClassicalSixthBranch.r = (124284256171281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1584
  · change upperPayment 1585 ≤ upperValue ((point split endpoint 4096 1585+point split endpoint 4096 1586)/2)
    have hp : upperPayment 1585 = (312669891210:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1585+point split endpoint 4096 1586)/2 = (616026877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616026877:ℝ)/168755200)*ClassicalSixthBranch.v ((616026877:ℝ)/168755200)/ClassicalSixthBranch.r = (124261447008537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1585
  · change upperPayment 1586 ≤ upperValue ((point split endpoint 4096 1586+point split endpoint 4096 1587)/2)
    have hp : upperPayment 1586 = (312581809313:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1586+point split endpoint 4096 1587)/2 = (616052027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616052027:ℝ)/168755200)*ClassicalSixthBranch.v ((616052027:ℝ)/168755200)/ClassicalSixthBranch.r = (124238639869865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1586
  · change upperPayment 1587 ≤ upperValue ((point split endpoint 4096 1587+point split endpoint 4096 1588)/2)
    have hp : upperPayment 1587 = (312493703168:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1587+point split endpoint 4096 1588)/2 = (616077177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616077177:ℝ)/168755200)*ClassicalSixthBranch.v ((616077177:ℝ)/168755200)/ClassicalSixthBranch.r = (124215834755265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1587
  · change upperPayment 1588 ≤ upperValue ((point split endpoint 4096 1588+point split endpoint 4096 1589)/2)
    have hp : upperPayment 1588 = (312405572770:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1588+point split endpoint 4096 1589)/2 = (616102327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616102327:ℝ)/168755200)*ClassicalSixthBranch.v ((616102327:ℝ)/168755200)/ClassicalSixthBranch.r = (124193031664737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1588
  · change upperPayment 1589 ≤ upperValue ((point split endpoint 4096 1589+point split endpoint 4096 1590)/2)
    have hp : upperPayment 1589 = (312317418114:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1589+point split endpoint 4096 1590)/2 = (616127477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616127477:ℝ)/168755200)*ClassicalSixthBranch.v ((616127477:ℝ)/168755200)/ClassicalSixthBranch.r = (124170230598281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1589
  · change upperPayment 1590 ≤ upperValue ((point split endpoint 4096 1590+point split endpoint 4096 1591)/2)
    have hp : upperPayment 1590 = (312229239197:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1590+point split endpoint 4096 1591)/2 = (616152627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616152627:ℝ)/168755200)*ClassicalSixthBranch.v ((616152627:ℝ)/168755200)/ClassicalSixthBranch.r = (124147431555897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1590
  · change upperPayment 1591 ≤ upperValue ((point split endpoint 4096 1591+point split endpoint 4096 1592)/2)
    have hp : upperPayment 1591 = (312141036014:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1591+point split endpoint 4096 1592)/2 = (616177777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616177777:ℝ)/168755200)*ClassicalSixthBranch.v ((616177777:ℝ)/168755200)/ClassicalSixthBranch.r = (124124634537585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1591
  · change upperPayment 1592 ≤ upperValue ((point split endpoint 4096 1592+point split endpoint 4096 1593)/2)
    have hp : upperPayment 1592 = (312052808560:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1592+point split endpoint 4096 1593)/2 = (616202927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616202927:ℝ)/168755200)*ClassicalSixthBranch.v ((616202927:ℝ)/168755200)/ClassicalSixthBranch.r = (124101839543345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1592
  · change upperPayment 1593 ≤ upperValue ((point split endpoint 4096 1593+point split endpoint 4096 1594)/2)
    have hp : upperPayment 1593 = (311964556832:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1593+point split endpoint 4096 1594)/2 = (616228077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616228077:ℝ)/168755200)*ClassicalSixthBranch.v ((616228077:ℝ)/168755200)/ClassicalSixthBranch.r = (124079046573177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1593
  · change upperPayment 1594 ≤ upperValue ((point split endpoint 4096 1594+point split endpoint 4096 1595)/2)
    have hp : upperPayment 1594 = (311876280824:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1594+point split endpoint 4096 1595)/2 = (616253227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616253227:ℝ)/168755200)*ClassicalSixthBranch.v ((616253227:ℝ)/168755200)/ClassicalSixthBranch.r = (124056255627081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1594
  · change upperPayment 1595 ≤ upperValue ((point split endpoint 4096 1595+point split endpoint 4096 1596)/2)
    have hp : upperPayment 1595 = (311787980533:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1595+point split endpoint 4096 1596)/2 = (616278377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616278377:ℝ)/168755200)*ClassicalSixthBranch.v ((616278377:ℝ)/168755200)/ClassicalSixthBranch.r = (124033466705057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1595
  · change upperPayment 1596 ≤ upperValue ((point split endpoint 4096 1596+point split endpoint 4096 1597)/2)
    have hp : upperPayment 1596 = (311699655954:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1596+point split endpoint 4096 1597)/2 = (616303527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616303527:ℝ)/168755200)*ClassicalSixthBranch.v ((616303527:ℝ)/168755200)/ClassicalSixthBranch.r = (124010679807105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1596
  · change upperPayment 1597 ≤ upperValue ((point split endpoint 4096 1597+point split endpoint 4096 1598)/2)
    have hp : upperPayment 1597 = (311611307083:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1597+point split endpoint 4096 1598)/2 = (616328677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616328677:ℝ)/168755200)*ClassicalSixthBranch.v ((616328677:ℝ)/168755200)/ClassicalSixthBranch.r = (123987894933225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1597
  · change upperPayment 1598 ≤ upperValue ((point split endpoint 4096 1598+point split endpoint 4096 1599)/2)
    have hp : upperPayment 1598 = (311522933914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1598+point split endpoint 4096 1599)/2 = (616353827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616353827:ℝ)/168755200)*ClassicalSixthBranch.v ((616353827:ℝ)/168755200)/ClassicalSixthBranch.r = (123965112083417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1598
  · change upperPayment 1599 ≤ upperValue ((point split endpoint 4096 1599+point split endpoint 4096 1600)/2)
    have hp : upperPayment 1599 = (311434536445:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1599+point split endpoint 4096 1600)/2 = (616378977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616378977:ℝ)/168755200)*ClassicalSixthBranch.v ((616378977:ℝ)/168755200)/ClassicalSixthBranch.r = (123942331257681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1599
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_099
