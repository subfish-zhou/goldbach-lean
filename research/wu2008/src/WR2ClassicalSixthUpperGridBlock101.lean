import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints101
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_101 (j : Fin 16) : upperPayment (16*101+j.val) ≤
    upperValue ((point split endpoint 4096 (16*101+j.val)+point split endpoint 4096 (16*101+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1616 ≤ upperValue ((point split endpoint 4096 1616+point split endpoint 4096 1617)/2)
    have hp : upperPayment 1616 = (309928057128:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1616+point split endpoint 4096 1617)/2 = (616806527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616806527:ℝ)/168755200)*ClassicalSixthBranch.v ((616806527:ℝ)/168755200)/ClassicalSixthBranch.r = (123555366903185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1616
  · change upperPayment 1617 ≤ upperValue ((point split endpoint 4096 1617+point split endpoint 4096 1618)/2)
    have hp : upperPayment 1617 = (309839221485:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1617+point split endpoint 4096 1618)/2 = (616831677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616831677:ℝ)/168755200)*ClassicalSixthBranch.v ((616831677:ℝ)/168755200)/ClassicalSixthBranch.r = (123532622510745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1617
  · change upperPayment 1618 ≤ upperValue ((point split endpoint 4096 1618+point split endpoint 4096 1619)/2)
    have hp : upperPayment 1618 = (309750361457:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1618+point split endpoint 4096 1619)/2 = (616856827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616856827:ℝ)/168755200)*ClassicalSixthBranch.v ((616856827:ℝ)/168755200)/ClassicalSixthBranch.r = (123509880142377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1618
  · change upperPayment 1619 ≤ upperValue ((point split endpoint 4096 1619+point split endpoint 4096 1620)/2)
    have hp : upperPayment 1619 = (309661477040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1619+point split endpoint 4096 1620)/2 = (616881977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616881977:ℝ)/168755200)*ClassicalSixthBranch.v ((616881977:ℝ)/168755200)/ClassicalSixthBranch.r = (123487139798081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1619
  · change upperPayment 1620 ≤ upperValue ((point split endpoint 4096 1620+point split endpoint 4096 1621)/2)
    have hp : upperPayment 1620 = (309572568229:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1620+point split endpoint 4096 1621)/2 = (616907127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616907127:ℝ)/168755200)*ClassicalSixthBranch.v ((616907127:ℝ)/168755200)/ClassicalSixthBranch.r = (123464401477857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1620
  · change upperPayment 1621 ≤ upperValue ((point split endpoint 4096 1621+point split endpoint 4096 1622)/2)
    have hp : upperPayment 1621 = (309483635020:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1621+point split endpoint 4096 1622)/2 = (616932277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616932277:ℝ)/168755200)*ClassicalSixthBranch.v ((616932277:ℝ)/168755200)/ClassicalSixthBranch.r = (123441665181705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1621
  · change upperPayment 1622 ≤ upperValue ((point split endpoint 4096 1622+point split endpoint 4096 1623)/2)
    have hp : upperPayment 1622 = (309394677408:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1622+point split endpoint 4096 1623)/2 = (616957427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616957427:ℝ)/168755200)*ClassicalSixthBranch.v ((616957427:ℝ)/168755200)/ClassicalSixthBranch.r = (123418930909625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1622
  · change upperPayment 1623 ≤ upperValue ((point split endpoint 4096 1623+point split endpoint 4096 1624)/2)
    have hp : upperPayment 1623 = (309305695389:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1623+point split endpoint 4096 1624)/2 = (616982577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616982577:ℝ)/168755200)*ClassicalSixthBranch.v ((616982577:ℝ)/168755200)/ClassicalSixthBranch.r = (123396198661617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1623
  · change upperPayment 1624 ≤ upperValue ((point split endpoint 4096 1624+point split endpoint 4096 1625)/2)
    have hp : upperPayment 1624 = (309216688958:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1624+point split endpoint 4096 1625)/2 = (617007727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617007727:ℝ)/168755200)*ClassicalSixthBranch.v ((617007727:ℝ)/168755200)/ClassicalSixthBranch.r = (123373468437681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1624
  · change upperPayment 1625 ≤ upperValue ((point split endpoint 4096 1625+point split endpoint 4096 1626)/2)
    have hp : upperPayment 1625 = (309127658112:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1625+point split endpoint 4096 1626)/2 = (617032877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617032877:ℝ)/168755200)*ClassicalSixthBranch.v ((617032877:ℝ)/168755200)/ClassicalSixthBranch.r = (123350740237817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1625
  · change upperPayment 1626 ≤ upperValue ((point split endpoint 4096 1626+point split endpoint 4096 1627)/2)
    have hp : upperPayment 1626 = (309038602845:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1626+point split endpoint 4096 1627)/2 = (617058027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617058027:ℝ)/168755200)*ClassicalSixthBranch.v ((617058027:ℝ)/168755200)/ClassicalSixthBranch.r = (123328014062025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1626
  · change upperPayment 1627 ≤ upperValue ((point split endpoint 4096 1627+point split endpoint 4096 1628)/2)
    have hp : upperPayment 1627 = (308949523153:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1627+point split endpoint 4096 1628)/2 = (617083177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617083177:ℝ)/168755200)*ClassicalSixthBranch.v ((617083177:ℝ)/168755200)/ClassicalSixthBranch.r = (123305289910305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1627
  · change upperPayment 1628 ≤ upperValue ((point split endpoint 4096 1628+point split endpoint 4096 1629)/2)
    have hp : upperPayment 1628 = (308860419032:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1628+point split endpoint 4096 1629)/2 = (617108327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617108327:ℝ)/168755200)*ClassicalSixthBranch.v ((617108327:ℝ)/168755200)/ClassicalSixthBranch.r = (123282567782657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1628
  · change upperPayment 1629 ≤ upperValue ((point split endpoint 4096 1629+point split endpoint 4096 1630)/2)
    have hp : upperPayment 1629 = (308771290477:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1629+point split endpoint 4096 1630)/2 = (617133477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617133477:ℝ)/168755200)*ClassicalSixthBranch.v ((617133477:ℝ)/168755200)/ClassicalSixthBranch.r = (123259847679081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1629
  · change upperPayment 1630 ≤ upperValue ((point split endpoint 4096 1630+point split endpoint 4096 1631)/2)
    have hp : upperPayment 1630 = (308682137484:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1630+point split endpoint 4096 1631)/2 = (617158627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617158627:ℝ)/168755200)*ClassicalSixthBranch.v ((617158627:ℝ)/168755200)/ClassicalSixthBranch.r = (123237129599577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1630
  · change upperPayment 1631 ≤ upperValue ((point split endpoint 4096 1631+point split endpoint 4096 1632)/2)
    have hp : upperPayment 1631 = (308592960048:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1631+point split endpoint 4096 1632)/2 = (617183777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617183777:ℝ)/168755200)*ClassicalSixthBranch.v ((617183777:ℝ)/168755200)/ClassicalSixthBranch.r = (123214413544145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1631
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_101
