import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints102
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_102 (j : Fin 16) : upperPayment (16*102+j.val) ≤
    upperValue ((point split endpoint 4096 (16*102+j.val)+point split endpoint 4096 (16*102+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1632 ≤ upperValue ((point split endpoint 4096 1632+point split endpoint 4096 1633)/2)
    have hp : upperPayment 1632 = (308503758165:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1632+point split endpoint 4096 1633)/2 = (617208927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617208927:ℝ)/168755200)*ClassicalSixthBranch.v ((617208927:ℝ)/168755200)/ClassicalSixthBranch.r = (123191699512785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1632
  · change upperPayment 1633 ≤ upperValue ((point split endpoint 4096 1633+point split endpoint 4096 1634)/2)
    have hp : upperPayment 1633 = (308414531830:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1633+point split endpoint 4096 1634)/2 = (617234077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617234077:ℝ)/168755200)*ClassicalSixthBranch.v ((617234077:ℝ)/168755200)/ClassicalSixthBranch.r = (123168987505497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1633
  · change upperPayment 1634 ≤ upperValue ((point split endpoint 4096 1634+point split endpoint 4096 1635)/2)
    have hp : upperPayment 1634 = (308325281040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1634+point split endpoint 4096 1635)/2 = (617259227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617259227:ℝ)/168755200)*ClassicalSixthBranch.v ((617259227:ℝ)/168755200)/ClassicalSixthBranch.r = (123146277522281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1634
  · change upperPayment 1635 ≤ upperValue ((point split endpoint 4096 1635+point split endpoint 4096 1636)/2)
    have hp : upperPayment 1635 = (308236005789:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1635+point split endpoint 4096 1636)/2 = (617284377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617284377:ℝ)/168755200)*ClassicalSixthBranch.v ((617284377:ℝ)/168755200)/ClassicalSixthBranch.r = (123123569563137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1635
  · change upperPayment 1636 ≤ upperValue ((point split endpoint 4096 1636+point split endpoint 4096 1637)/2)
    have hp : upperPayment 1636 = (308146706073:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1636+point split endpoint 4096 1637)/2 = (617309527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617309527:ℝ)/168755200)*ClassicalSixthBranch.v ((617309527:ℝ)/168755200)/ClassicalSixthBranch.r = (123100863628065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1636
  · change upperPayment 1637 ≤ upperValue ((point split endpoint 4096 1637+point split endpoint 4096 1638)/2)
    have hp : upperPayment 1637 = (308057381888:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1637+point split endpoint 4096 1638)/2 = (617334677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617334677:ℝ)/168755200)*ClassicalSixthBranch.v ((617334677:ℝ)/168755200)/ClassicalSixthBranch.r = (123078159717065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1637
  · change upperPayment 1638 ≤ upperValue ((point split endpoint 4096 1638+point split endpoint 4096 1639)/2)
    have hp : upperPayment 1638 = (307968033228:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1638+point split endpoint 4096 1639)/2 = (617359827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617359827:ℝ)/168755200)*ClassicalSixthBranch.v ((617359827:ℝ)/168755200)/ClassicalSixthBranch.r = (123055457830137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1638
  · change upperPayment 1639 ≤ upperValue ((point split endpoint 4096 1639+point split endpoint 4096 1640)/2)
    have hp : upperPayment 1639 = (307878660091:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1639+point split endpoint 4096 1640)/2 = (617384977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617384977:ℝ)/168755200)*ClassicalSixthBranch.v ((617384977:ℝ)/168755200)/ClassicalSixthBranch.r = (123032757967281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1639
  · change upperPayment 1640 ≤ upperValue ((point split endpoint 4096 1640+point split endpoint 4096 1641)/2)
    have hp : upperPayment 1640 = (307789262471:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1640+point split endpoint 4096 1641)/2 = (617410127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617410127:ℝ)/168755200)*ClassicalSixthBranch.v ((617410127:ℝ)/168755200)/ClassicalSixthBranch.r = (123010060128497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1640
  · change upperPayment 1641 ≤ upperValue ((point split endpoint 4096 1641+point split endpoint 4096 1642)/2)
    have hp : upperPayment 1641 = (307699840363:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1641+point split endpoint 4096 1642)/2 = (617435277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617435277:ℝ)/168755200)*ClassicalSixthBranch.v ((617435277:ℝ)/168755200)/ClassicalSixthBranch.r = (122987364313785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1641
  · change upperPayment 1642 ≤ upperValue ((point split endpoint 4096 1642+point split endpoint 4096 1643)/2)
    have hp : upperPayment 1642 = (307610393764:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1642+point split endpoint 4096 1643)/2 = (617460427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617460427:ℝ)/168755200)*ClassicalSixthBranch.v ((617460427:ℝ)/168755200)/ClassicalSixthBranch.r = (122964670523145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1642
  · change upperPayment 1643 ≤ upperValue ((point split endpoint 4096 1643+point split endpoint 4096 1644)/2)
    have hp : upperPayment 1643 = (307520922668:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1643+point split endpoint 4096 1644)/2 = (617485577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617485577:ℝ)/168755200)*ClassicalSixthBranch.v ((617485577:ℝ)/168755200)/ClassicalSixthBranch.r = (122941978756577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1643
  · change upperPayment 1644 ≤ upperValue ((point split endpoint 4096 1644+point split endpoint 4096 1645)/2)
    have hp : upperPayment 1644 = (307431427072:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1644+point split endpoint 4096 1645)/2 = (617510727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617510727:ℝ)/168755200)*ClassicalSixthBranch.v ((617510727:ℝ)/168755200)/ClassicalSixthBranch.r = (122919289014081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1644
  · change upperPayment 1645 ≤ upperValue ((point split endpoint 4096 1645+point split endpoint 4096 1646)/2)
    have hp : upperPayment 1645 = (307341906970:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1645+point split endpoint 4096 1646)/2 = (617535877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617535877:ℝ)/168755200)*ClassicalSixthBranch.v ((617535877:ℝ)/168755200)/ClassicalSixthBranch.r = (122896601295657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1645
  · change upperPayment 1646 ≤ upperValue ((point split endpoint 4096 1646+point split endpoint 4096 1647)/2)
    have hp : upperPayment 1646 = (307252362359:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1646+point split endpoint 4096 1647)/2 = (617561027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617561027:ℝ)/168755200)*ClassicalSixthBranch.v ((617561027:ℝ)/168755200)/ClassicalSixthBranch.r = (122873915601305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1646
  · change upperPayment 1647 ≤ upperValue ((point split endpoint 4096 1647+point split endpoint 4096 1648)/2)
    have hp : upperPayment 1647 = (307162793234:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1647+point split endpoint 4096 1648)/2 = (617586177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((617586177:ℝ)/168755200)*ClassicalSixthBranch.v ((617586177:ℝ)/168755200)/ClassicalSixthBranch.r = (122851231931025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1647
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_102
