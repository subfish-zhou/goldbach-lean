import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints093
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_093 (j : Fin 16) : upperPayment (16*93+j.val) ≤
    upperValue ((point split endpoint 4096 (16*93+j.val)+point split endpoint 4096 (16*93+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1488 ≤ upperValue ((point split endpoint 4096 1488+point split endpoint 4096 1489)/2)
    have hp : upperPayment 1488 = (321099260780:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1488+point split endpoint 4096 1489)/2 = (613587327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613587327:ℝ)/168755200)*ClassicalSixthBranch.v ((613587327:ℝ)/168755200)/ClassicalSixthBranch.r = (126483359873937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1488
  · change upperPayment 1489 ≤ upperValue ((point split endpoint 4096 1489+point split endpoint 4096 1490)/2)
    have hp : upperPayment 1489 = (321013510486:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1489+point split endpoint 4096 1490)/2 = (613612477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613612477:ℝ)/168755200)*ClassicalSixthBranch.v ((613612477:ℝ)/168755200)/ClassicalSixthBranch.r = (126460356400281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1489
  · change upperPayment 1490 ≤ upperValue ((point split endpoint 4096 1490+point split endpoint 4096 1491)/2)
    have hp : upperPayment 1490 = (320927736360:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1490+point split endpoint 4096 1491)/2 = (613637627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613637627:ℝ)/168755200)*ClassicalSixthBranch.v ((613637627:ℝ)/168755200)/ClassicalSixthBranch.r = (126437354950697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1490
  · change upperPayment 1491 ≤ upperValue ((point split endpoint 4096 1491+point split endpoint 4096 1492)/2)
    have hp : upperPayment 1491 = (320841938397:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1491+point split endpoint 4096 1492)/2 = (613662777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613662777:ℝ)/168755200)*ClassicalSixthBranch.v ((613662777:ℝ)/168755200)/ClassicalSixthBranch.r = (126414355525185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1491
  · change upperPayment 1492 ≤ upperValue ((point split endpoint 4096 1492+point split endpoint 4096 1493)/2)
    have hp : upperPayment 1492 = (320756116593:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1492+point split endpoint 4096 1493)/2 = (613687927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613687927:ℝ)/168755200)*ClassicalSixthBranch.v ((613687927:ℝ)/168755200)/ClassicalSixthBranch.r = (126391358123745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1492
  · change upperPayment 1493 ≤ upperValue ((point split endpoint 4096 1493+point split endpoint 4096 1494)/2)
    have hp : upperPayment 1493 = (320670270943:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1493+point split endpoint 4096 1494)/2 = (613713077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613713077:ℝ)/168755200)*ClassicalSixthBranch.v ((613713077:ℝ)/168755200)/ClassicalSixthBranch.r = (126368362746377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1493
  · change upperPayment 1494 ≤ upperValue ((point split endpoint 4096 1494+point split endpoint 4096 1495)/2)
    have hp : upperPayment 1494 = (320584401444:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1494+point split endpoint 4096 1495)/2 = (613738227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613738227:ℝ)/168755200)*ClassicalSixthBranch.v ((613738227:ℝ)/168755200)/ClassicalSixthBranch.r = (126345369393081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1494
  · change upperPayment 1495 ≤ upperValue ((point split endpoint 4096 1495+point split endpoint 4096 1496)/2)
    have hp : upperPayment 1495 = (320498508090:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1495+point split endpoint 4096 1496)/2 = (613763377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613763377:ℝ)/168755200)*ClassicalSixthBranch.v ((613763377:ℝ)/168755200)/ClassicalSixthBranch.r = (126322378063857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1495
  · change upperPayment 1496 ≤ upperValue ((point split endpoint 4096 1496+point split endpoint 4096 1497)/2)
    have hp : upperPayment 1496 = (320412590879:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1496+point split endpoint 4096 1497)/2 = (613788527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613788527:ℝ)/168755200)*ClassicalSixthBranch.v ((613788527:ℝ)/168755200)/ClassicalSixthBranch.r = (126299388758705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1496
  · change upperPayment 1497 ≤ upperValue ((point split endpoint 4096 1497+point split endpoint 4096 1498)/2)
    have hp : upperPayment 1497 = (320326649806:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1497+point split endpoint 4096 1498)/2 = (613813677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613813677:ℝ)/168755200)*ClassicalSixthBranch.v ((613813677:ℝ)/168755200)/ClassicalSixthBranch.r = (126276401477625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1497
  · change upperPayment 1498 ≤ upperValue ((point split endpoint 4096 1498+point split endpoint 4096 1499)/2)
    have hp : upperPayment 1498 = (320240684866:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1498+point split endpoint 4096 1499)/2 = (613838827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613838827:ℝ)/168755200)*ClassicalSixthBranch.v ((613838827:ℝ)/168755200)/ClassicalSixthBranch.r = (126253416220617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1498
  · change upperPayment 1499 ≤ upperValue ((point split endpoint 4096 1499+point split endpoint 4096 1500)/2)
    have hp : upperPayment 1499 = (320154696055:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1499+point split endpoint 4096 1500)/2 = (613863977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613863977:ℝ)/168755200)*ClassicalSixthBranch.v ((613863977:ℝ)/168755200)/ClassicalSixthBranch.r = (126230432987681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1499
  · change upperPayment 1500 ≤ upperValue ((point split endpoint 4096 1500+point split endpoint 4096 1501)/2)
    have hp : upperPayment 1500 = (320068683369:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1500+point split endpoint 4096 1501)/2 = (613889127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613889127:ℝ)/168755200)*ClassicalSixthBranch.v ((613889127:ℝ)/168755200)/ClassicalSixthBranch.r = (126207451778817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1500
  · change upperPayment 1501 ≤ upperValue ((point split endpoint 4096 1501+point split endpoint 4096 1502)/2)
    have hp : upperPayment 1501 = (319982646804:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1501+point split endpoint 4096 1502)/2 = (613914277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613914277:ℝ)/168755200)*ClassicalSixthBranch.v ((613914277:ℝ)/168755200)/ClassicalSixthBranch.r = (126184472594025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1501
  · change upperPayment 1502 ≤ upperValue ((point split endpoint 4096 1502+point split endpoint 4096 1503)/2)
    have hp : upperPayment 1502 = (319896586356:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1502+point split endpoint 4096 1503)/2 = (613939427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613939427:ℝ)/168755200)*ClassicalSixthBranch.v ((613939427:ℝ)/168755200)/ClassicalSixthBranch.r = (126161495433305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1502
  · change upperPayment 1503 ≤ upperValue ((point split endpoint 4096 1503+point split endpoint 4096 1504)/2)
    have hp : upperPayment 1503 = (319810502020:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1503+point split endpoint 4096 1504)/2 = (613964577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613964577:ℝ)/168755200)*ClassicalSixthBranch.v ((613964577:ℝ)/168755200)/ClassicalSixthBranch.r = (126138520296657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1503
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_093
