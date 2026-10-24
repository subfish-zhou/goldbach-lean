import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints098
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_098 (j : Fin 16) : upperPayment (16*98+j.val) ≤
    upperValue ((point split endpoint 4096 (16*98+j.val)+point split endpoint 4096 (16*98+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1568 ≤ upperValue ((point split endpoint 4096 1568+point split endpoint 4096 1569)/2)
    have hp : upperPayment 1568 = (314163577657:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1568+point split endpoint 4096 1569)/2 = (615599327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615599327:ℝ)/168755200)*ClassicalSixthBranch.v ((615599327:ℝ)/168755200)/ClassicalSixthBranch.r = (124649478048977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1568
  · change upperPayment 1569 ≤ upperValue ((point split endpoint 4096 1569+point split endpoint 4096 1570)/2)
    have hp : upperPayment 1569 = (314075907318:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1569+point split endpoint 4096 1570)/2 = (615624477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615624477:ℝ)/168755200)*ClassicalSixthBranch.v ((615624477:ℝ)/168755200)/ClassicalSixthBranch.r = (124626636501081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1569
  · change upperPayment 1570 ≤ upperValue ((point split endpoint 4096 1570+point split endpoint 4096 1571)/2)
    have hp : upperPayment 1570 = (313988212804:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1570+point split endpoint 4096 1571)/2 = (615649627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615649627:ℝ)/168755200)*ClassicalSixthBranch.v ((615649627:ℝ)/168755200)/ClassicalSixthBranch.r = (124603796977257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1570
  · change upperPayment 1571 ≤ upperValue ((point split endpoint 4096 1571+point split endpoint 4096 1572)/2)
    have hp : upperPayment 1571 = (313900494112:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1571+point split endpoint 4096 1572)/2 = (615674777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615674777:ℝ)/168755200)*ClassicalSixthBranch.v ((615674777:ℝ)/168755200)/ClassicalSixthBranch.r = (124580959477505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1571
  · change upperPayment 1572 ≤ upperValue ((point split endpoint 4096 1572+point split endpoint 4096 1573)/2)
    have hp : upperPayment 1572 = (313812751237:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1572+point split endpoint 4096 1573)/2 = (615699927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615699927:ℝ)/168755200)*ClassicalSixthBranch.v ((615699927:ℝ)/168755200)/ClassicalSixthBranch.r = (1209302174775:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1572
  · change upperPayment 1573 ≤ upperValue ((point split endpoint 4096 1573+point split endpoint 4096 1574)/2)
    have hp : upperPayment 1573 = (313724984174:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1573+point split endpoint 4096 1574)/2 = (615725077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615725077:ℝ)/168755200)*ClassicalSixthBranch.v ((615725077:ℝ)/168755200)/ClassicalSixthBranch.r = (124535290550217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1573
  · change upperPayment 1574 ≤ upperValue ((point split endpoint 4096 1574+point split endpoint 4096 1575)/2)
    have hp : upperPayment 1574 = (313637192919:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1574+point split endpoint 4096 1575)/2 = (615750227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615750227:ℝ)/168755200)*ClassicalSixthBranch.v ((615750227:ℝ)/168755200)/ClassicalSixthBranch.r = (124512459122681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1574
  · change upperPayment 1575 ≤ upperValue ((point split endpoint 4096 1575+point split endpoint 4096 1576)/2)
    have hp : upperPayment 1575 = (313549377468:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1575+point split endpoint 4096 1576)/2 = (615775377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615775377:ℝ)/168755200)*ClassicalSixthBranch.v ((615775377:ℝ)/168755200)/ClassicalSixthBranch.r = (124489629719217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1575
  · change upperPayment 1576 ≤ upperValue ((point split endpoint 4096 1576+point split endpoint 4096 1577)/2)
    have hp : upperPayment 1576 = (313461537817:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1576+point split endpoint 4096 1577)/2 = (615800527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615800527:ℝ)/168755200)*ClassicalSixthBranch.v ((615800527:ℝ)/168755200)/ClassicalSixthBranch.r = (124466802339825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1576
  · change upperPayment 1577 ≤ upperValue ((point split endpoint 4096 1577+point split endpoint 4096 1578)/2)
    have hp : upperPayment 1577 = (313373673960:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1577+point split endpoint 4096 1578)/2 = (615825677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615825677:ℝ)/168755200)*ClassicalSixthBranch.v ((615825677:ℝ)/168755200)/ClassicalSixthBranch.r = (124443976984505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1577
  · change upperPayment 1578 ≤ upperValue ((point split endpoint 4096 1578+point split endpoint 4096 1579)/2)
    have hp : upperPayment 1578 = (313285785895:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1578+point split endpoint 4096 1579)/2 = (615850827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615850827:ℝ)/168755200)*ClassicalSixthBranch.v ((615850827:ℝ)/168755200)/ClassicalSixthBranch.r = (124421153653257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1578
  · change upperPayment 1579 ≤ upperValue ((point split endpoint 4096 1579+point split endpoint 4096 1580)/2)
    have hp : upperPayment 1579 = (313197873615:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1579+point split endpoint 4096 1580)/2 = (615875977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615875977:ℝ)/168755200)*ClassicalSixthBranch.v ((615875977:ℝ)/168755200)/ClassicalSixthBranch.r = (124398332346081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1579
  · change upperPayment 1580 ≤ upperValue ((point split endpoint 4096 1580+point split endpoint 4096 1581)/2)
    have hp : upperPayment 1580 = (313109937118:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1580+point split endpoint 4096 1581)/2 = (615901127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615901127:ℝ)/168755200)*ClassicalSixthBranch.v ((615901127:ℝ)/168755200)/ClassicalSixthBranch.r = (124375513062977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1580
  · change upperPayment 1581 ≤ upperValue ((point split endpoint 4096 1581+point split endpoint 4096 1582)/2)
    have hp : upperPayment 1581 = (313021976399:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1581+point split endpoint 4096 1582)/2 = (615926277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615926277:ℝ)/168755200)*ClassicalSixthBranch.v ((615926277:ℝ)/168755200)/ClassicalSixthBranch.r = (124352695803945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1581
  · change upperPayment 1582 ≤ upperValue ((point split endpoint 4096 1582+point split endpoint 4096 1583)/2)
    have hp : upperPayment 1582 = (312933991452:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1582+point split endpoint 4096 1583)/2 = (615951427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615951427:ℝ)/168755200)*ClassicalSixthBranch.v ((615951427:ℝ)/168755200)/ClassicalSixthBranch.r = (124329880568985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1582
  · change upperPayment 1583 ≤ upperValue ((point split endpoint 4096 1583+point split endpoint 4096 1584)/2)
    have hp : upperPayment 1583 = (312845982275:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1583+point split endpoint 4096 1584)/2 = (615976577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615976577:ℝ)/168755200)*ClassicalSixthBranch.v ((615976577:ℝ)/168755200)/ClassicalSixthBranch.r = (124307067358097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1583
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_098
