import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints097
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_097 (j : Fin 16) : upperPayment (16*97+j.val) ≤
    upperValue ((point split endpoint 4096 (16*97+j.val)+point split endpoint 4096 (16*97+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1552 ≤ upperValue ((point split endpoint 4096 1552+point split endpoint 4096 1553)/2)
    have hp : upperPayment 1552 = (315563018888:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1552+point split endpoint 4096 1553)/2 = (615196927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615196927:ℝ)/168755200)*ClassicalSixthBranch.v ((615196927:ℝ)/168755200)/ClassicalSixthBranch.r = (125015218089105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1552
  · change upperPayment 1553 ≤ upperValue ((point split endpoint 4096 1553+point split endpoint 4096 1554)/2)
    have hp : upperPayment 1553 = (315475734752:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1553+point split endpoint 4096 1554)/2 = (615222077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615222077:ℝ)/168755200)*ClassicalSixthBranch.v ((615222077:ℝ)/168755200)/ClassicalSixthBranch.r = (124992344156057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1553
  · change upperPayment 1554 ≤ upperValue ((point split endpoint 4096 1554+point split endpoint 4096 1555)/2)
    have hp : upperPayment 1554 = (315388426510:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1554+point split endpoint 4096 1555)/2 = (615247227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615247227:ℝ)/168755200)*ClassicalSixthBranch.v ((615247227:ℝ)/168755200)/ClassicalSixthBranch.r = (124969472247081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1554
  · change upperPayment 1555 ≤ upperValue ((point split endpoint 4096 1555+point split endpoint 4096 1556)/2)
    have hp : upperPayment 1555 = (315301094159:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1555+point split endpoint 4096 1556)/2 = (615272377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615272377:ℝ)/168755200)*ClassicalSixthBranch.v ((615272377:ℝ)/168755200)/ClassicalSixthBranch.r = (124946602362177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1555
  · change upperPayment 1556 ≤ upperValue ((point split endpoint 4096 1556+point split endpoint 4096 1557)/2)
    have hp : upperPayment 1556 = (315213737694:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1556+point split endpoint 4096 1557)/2 = (615297527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615297527:ℝ)/168755200)*ClassicalSixthBranch.v ((615297527:ℝ)/168755200)/ClassicalSixthBranch.r = (124923734501345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1556
  · change upperPayment 1557 ≤ upperValue ((point split endpoint 4096 1557+point split endpoint 4096 1558)/2)
    have hp : upperPayment 1557 = (315126357110:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1557+point split endpoint 4096 1558)/2 = (615322677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615322677:ℝ)/168755200)*ClassicalSixthBranch.v ((615322677:ℝ)/168755200)/ClassicalSixthBranch.r = (124900868664585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1557
  · change upperPayment 1558 ≤ upperValue ((point split endpoint 4096 1558+point split endpoint 4096 1559)/2)
    have hp : upperPayment 1558 = (315038952404:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1558+point split endpoint 4096 1559)/2 = (615347827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615347827:ℝ)/168755200)*ClassicalSixthBranch.v ((615347827:ℝ)/168755200)/ClassicalSixthBranch.r = (124878004851897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1558
  · change upperPayment 1559 ≤ upperValue ((point split endpoint 4096 1559+point split endpoint 4096 1560)/2)
    have hp : upperPayment 1559 = (314951523572:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1559+point split endpoint 4096 1560)/2 = (615372977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615372977:ℝ)/168755200)*ClassicalSixthBranch.v ((615372977:ℝ)/168755200)/ClassicalSixthBranch.r = (124855143063281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1559
  · change upperPayment 1560 ≤ upperValue ((point split endpoint 4096 1560+point split endpoint 4096 1561)/2)
    have hp : upperPayment 1560 = (314864070608:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1560+point split endpoint 4096 1561)/2 = (615398127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615398127:ℝ)/168755200)*ClassicalSixthBranch.v ((615398127:ℝ)/168755200)/ClassicalSixthBranch.r = (124832283298737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1560
  · change upperPayment 1561 ≤ upperValue ((point split endpoint 4096 1561+point split endpoint 4096 1562)/2)
    have hp : upperPayment 1561 = (314776593509:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1561+point split endpoint 4096 1562)/2 = (615423277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615423277:ℝ)/168755200)*ClassicalSixthBranch.v ((615423277:ℝ)/168755200)/ClassicalSixthBranch.r = (124809425558265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1561
  · change upperPayment 1562 ≤ upperValue ((point split endpoint 4096 1562+point split endpoint 4096 1563)/2)
    have hp : upperPayment 1562 = (314689092269:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1562+point split endpoint 4096 1563)/2 = (615448427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615448427:ℝ)/168755200)*ClassicalSixthBranch.v ((615448427:ℝ)/168755200)/ClassicalSixthBranch.r = (124786569841865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1562
  · change upperPayment 1563 ≤ upperValue ((point split endpoint 4096 1563+point split endpoint 4096 1564)/2)
    have hp : upperPayment 1563 = (314601566886:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1563+point split endpoint 4096 1564)/2 = (615473577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615473577:ℝ)/168755200)*ClassicalSixthBranch.v ((615473577:ℝ)/168755200)/ClassicalSixthBranch.r = (124763716149537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1563
  · change upperPayment 1564 ≤ upperValue ((point split endpoint 4096 1564+point split endpoint 4096 1565)/2)
    have hp : upperPayment 1564 = (314514017355:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1564+point split endpoint 4096 1565)/2 = (615498727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615498727:ℝ)/168755200)*ClassicalSixthBranch.v ((615498727:ℝ)/168755200)/ClassicalSixthBranch.r = (124740864481281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1564
  · change upperPayment 1565 ≤ upperValue ((point split endpoint 4096 1565+point split endpoint 4096 1566)/2)
    have hp : upperPayment 1565 = (314426443670:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1565+point split endpoint 4096 1566)/2 = (615523877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615523877:ℝ)/168755200)*ClassicalSixthBranch.v ((615523877:ℝ)/168755200)/ClassicalSixthBranch.r = (124718014837097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1565
  · change upperPayment 1566 ≤ upperValue ((point split endpoint 4096 1566+point split endpoint 4096 1567)/2)
    have hp : upperPayment 1566 = (314338845829:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1566+point split endpoint 4096 1567)/2 = (615549027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615549027:ℝ)/168755200)*ClassicalSixthBranch.v ((615549027:ℝ)/168755200)/ClassicalSixthBranch.r = (124695167216985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1566
  · change upperPayment 1567 ≤ upperValue ((point split endpoint 4096 1567+point split endpoint 4096 1568)/2)
    have hp : upperPayment 1567 = (314251223826:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1567+point split endpoint 4096 1568)/2 = (615574177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((615574177:ℝ)/168755200)*ClassicalSixthBranch.v ((615574177:ℝ)/168755200)/ClassicalSixthBranch.r = (124672321620945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1567
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_097
