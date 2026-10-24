import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints095
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_095 (j : Fin 16) : upperPayment (16*95+j.val) ≤
    upperValue ((point split endpoint 4096 (16*95+j.val)+point split endpoint 4096 (16*95+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1520 ≤ upperValue ((point split endpoint 4096 1520+point split endpoint 4096 1521)/2)
    have hp : upperPayment 1520 = (318343409414:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1520+point split endpoint 4096 1521)/2 = (614392127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614392127:ℝ)/168755200)*ClassicalSixthBranch.v ((614392127:ℝ)/168755200)/ClassicalSixthBranch.r = (125748252656657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1520
  · change upperPayment 1521 ≤ upperValue ((point split endpoint 4096 1521+point split endpoint 4096 1522)/2)
    have hp : upperPayment 1521 = (318256894378:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1521+point split endpoint 4096 1522)/2 = (614417277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614417277:ℝ)/168755200)*ClassicalSixthBranch.v ((614417277:ℝ)/168755200)/ClassicalSixthBranch.r = (125725313953305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1521
  · change upperPayment 1522 ≤ upperValue ((point split endpoint 4096 1522+point split endpoint 4096 1523)/2)
    have hp : upperPayment 1522 = (318170355374:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1522+point split endpoint 4096 1523)/2 = (614442427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614442427:ℝ)/168755200)*ClassicalSixthBranch.v ((614442427:ℝ)/168755200)/ClassicalSixthBranch.r = (125702377274025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1522
  · change upperPayment 1523 ≤ upperValue ((point split endpoint 4096 1523+point split endpoint 4096 1524)/2)
    have hp : upperPayment 1523 = (318083792397:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1523+point split endpoint 4096 1524)/2 = (614467577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614467577:ℝ)/168755200)*ClassicalSixthBranch.v ((614467577:ℝ)/168755200)/ClassicalSixthBranch.r = (125679442618817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1523
  · change upperPayment 1524 ≤ upperValue ((point split endpoint 4096 1524+point split endpoint 4096 1525)/2)
    have hp : upperPayment 1524 = (317997205444:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1524+point split endpoint 4096 1525)/2 = (614492727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614492727:ℝ)/168755200)*ClassicalSixthBranch.v ((614492727:ℝ)/168755200)/ClassicalSixthBranch.r = (125656509987681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1524
  · change upperPayment 1525 ≤ upperValue ((point split endpoint 4096 1525+point split endpoint 4096 1526)/2)
    have hp : upperPayment 1525 = (317910594510:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1525+point split endpoint 4096 1526)/2 = (614517877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614517877:ℝ)/168755200)*ClassicalSixthBranch.v ((614517877:ℝ)/168755200)/ClassicalSixthBranch.r = (125633579380617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1525
  · change upperPayment 1526 ≤ upperValue ((point split endpoint 4096 1526+point split endpoint 4096 1527)/2)
    have hp : upperPayment 1526 = (317823959590:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1526+point split endpoint 4096 1527)/2 = (614543027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614543027:ℝ)/168755200)*ClassicalSixthBranch.v ((614543027:ℝ)/168755200)/ClassicalSixthBranch.r = (125610650797625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1526
  · change upperPayment 1527 ≤ upperValue ((point split endpoint 4096 1527+point split endpoint 4096 1528)/2)
    have hp : upperPayment 1527 = (317737300682:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1527+point split endpoint 4096 1528)/2 = (614568177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614568177:ℝ)/168755200)*ClassicalSixthBranch.v ((614568177:ℝ)/168755200)/ClassicalSixthBranch.r = (125587724238705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1527
  · change upperPayment 1528 ≤ upperValue ((point split endpoint 4096 1528+point split endpoint 4096 1529)/2)
    have hp : upperPayment 1528 = (317650617779:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1528+point split endpoint 4096 1529)/2 = (614593327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614593327:ℝ)/168755200)*ClassicalSixthBranch.v ((614593327:ℝ)/168755200)/ClassicalSixthBranch.r = (125564799703857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1528
  · change upperPayment 1529 ≤ upperValue ((point split endpoint 4096 1529+point split endpoint 4096 1530)/2)
    have hp : upperPayment 1529 = (317563910879:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1529+point split endpoint 4096 1530)/2 = (614618477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614618477:ℝ)/168755200)*ClassicalSixthBranch.v ((614618477:ℝ)/168755200)/ClassicalSixthBranch.r = (125541877193081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1529
  · change upperPayment 1530 ≤ upperValue ((point split endpoint 4096 1530+point split endpoint 4096 1531)/2)
    have hp : upperPayment 1530 = (317477179976:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1530+point split endpoint 4096 1531)/2 = (614643627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614643627:ℝ)/168755200)*ClassicalSixthBranch.v ((614643627:ℝ)/168755200)/ClassicalSixthBranch.r = (125518956706377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1530
  · change upperPayment 1531 ≤ upperValue ((point split endpoint 4096 1531+point split endpoint 4096 1532)/2)
    have hp : upperPayment 1531 = (317390425067:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1531+point split endpoint 4096 1532)/2 = (614668777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614668777:ℝ)/168755200)*ClassicalSixthBranch.v ((614668777:ℝ)/168755200)/ClassicalSixthBranch.r = (125496038243745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1531
  · change upperPayment 1532 ≤ upperValue ((point split endpoint 4096 1532+point split endpoint 4096 1533)/2)
    have hp : upperPayment 1532 = (317303646147:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1532+point split endpoint 4096 1533)/2 = (614693927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614693927:ℝ)/168755200)*ClassicalSixthBranch.v ((614693927:ℝ)/168755200)/ClassicalSixthBranch.r = (125473121805185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1532
  · change upperPayment 1533 ≤ upperValue ((point split endpoint 4096 1533+point split endpoint 4096 1534)/2)
    have hp : upperPayment 1533 = (317216843212:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1533+point split endpoint 4096 1534)/2 = (614719077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614719077:ℝ)/168755200)*ClassicalSixthBranch.v ((614719077:ℝ)/168755200)/ClassicalSixthBranch.r = (125450207390697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1533
  · change upperPayment 1534 ≤ upperValue ((point split endpoint 4096 1534+point split endpoint 4096 1535)/2)
    have hp : upperPayment 1534 = (317130016258:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1534+point split endpoint 4096 1535)/2 = (614744227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614744227:ℝ)/168755200)*ClassicalSixthBranch.v ((614744227:ℝ)/168755200)/ClassicalSixthBranch.r = (125427295000281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1534
  · change upperPayment 1535 ≤ upperValue ((point split endpoint 4096 1535+point split endpoint 4096 1536)/2)
    have hp : upperPayment 1535 = (317043165280:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1535+point split endpoint 4096 1536)/2 = (614769377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614769377:ℝ)/168755200)*ClassicalSixthBranch.v ((614769377:ℝ)/168755200)/ClassicalSixthBranch.r = (125404384633937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1535
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_095
