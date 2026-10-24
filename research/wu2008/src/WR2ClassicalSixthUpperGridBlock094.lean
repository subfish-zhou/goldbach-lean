import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints094
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_094 (j : Fin 16) : upperPayment (16*94+j.val) ≤
    upperValue ((point split endpoint 4096 (16*94+j.val)+point split endpoint 4096 (16*94+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1504 ≤ upperValue ((point split endpoint 4096 1504+point split endpoint 4096 1505)/2)
    have hp : upperPayment 1504 = (319724393793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1504+point split endpoint 4096 1505)/2 = (613989727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613989727:ℝ)/168755200)*ClassicalSixthBranch.v ((613989727:ℝ)/168755200)/ClassicalSixthBranch.r = (126115547184081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1504
  · change upperPayment 1505 ≤ upperValue ((point split endpoint 4096 1505+point split endpoint 4096 1506)/2)
    have hp : upperPayment 1505 = (319638261669:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1505+point split endpoint 4096 1506)/2 = (614014877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614014877:ℝ)/168755200)*ClassicalSixthBranch.v ((614014877:ℝ)/168755200)/ClassicalSixthBranch.r = (126092576095577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1505
  · change upperPayment 1506 ≤ upperValue ((point split endpoint 4096 1506+point split endpoint 4096 1507)/2)
    have hp : upperPayment 1506 = (319552105645:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1506+point split endpoint 4096 1507)/2 = (614040027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614040027:ℝ)/168755200)*ClassicalSixthBranch.v ((614040027:ℝ)/168755200)/ClassicalSixthBranch.r = (126069607031145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1506
  · change upperPayment 1507 ≤ upperValue ((point split endpoint 4096 1507+point split endpoint 4096 1508)/2)
    have hp : upperPayment 1507 = (319465925717:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1507+point split endpoint 4096 1508)/2 = (614065177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614065177:ℝ)/168755200)*ClassicalSixthBranch.v ((614065177:ℝ)/168755200)/ClassicalSixthBranch.r = (126046639990785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1507
  · change upperPayment 1508 ≤ upperValue ((point split endpoint 4096 1508+point split endpoint 4096 1509)/2)
    have hp : upperPayment 1508 = (319379721880:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1508+point split endpoint 4096 1509)/2 = (614090327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614090327:ℝ)/168755200)*ClassicalSixthBranch.v ((614090327:ℝ)/168755200)/ClassicalSixthBranch.r = (126023674974497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1508
  · change upperPayment 1509 ≤ upperValue ((point split endpoint 4096 1509+point split endpoint 4096 1510)/2)
    have hp : upperPayment 1509 = (319293494130:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1509+point split endpoint 4096 1510)/2 = (614115477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614115477:ℝ)/168755200)*ClassicalSixthBranch.v ((614115477:ℝ)/168755200)/ClassicalSixthBranch.r = (126000711982281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1509
  · change upperPayment 1510 ≤ upperValue ((point split endpoint 4096 1510+point split endpoint 4096 1511)/2)
    have hp : upperPayment 1510 = (319207242463:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1510+point split endpoint 4096 1511)/2 = (614140627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614140627:ℝ)/168755200)*ClassicalSixthBranch.v ((614140627:ℝ)/168755200)/ClassicalSixthBranch.r = (125977751014137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1510
  · change upperPayment 1511 ≤ upperValue ((point split endpoint 4096 1511+point split endpoint 4096 1512)/2)
    have hp : upperPayment 1511 = (319120966874:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1511+point split endpoint 4096 1512)/2 = (614165777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614165777:ℝ)/168755200)*ClassicalSixthBranch.v ((614165777:ℝ)/168755200)/ClassicalSixthBranch.r = (125954792070065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1511
  · change upperPayment 1512 ≤ upperValue ((point split endpoint 4096 1512+point split endpoint 4096 1513)/2)
    have hp : upperPayment 1512 = (319034667360:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1512+point split endpoint 4096 1513)/2 = (614190927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614190927:ℝ)/168755200)*ClassicalSixthBranch.v ((614190927:ℝ)/168755200)/ClassicalSixthBranch.r = (125931835150065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1512
  · change upperPayment 1513 ≤ upperValue ((point split endpoint 4096 1513+point split endpoint 4096 1514)/2)
    have hp : upperPayment 1513 = (318948343916:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1513+point split endpoint 4096 1514)/2 = (614216077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614216077:ℝ)/168755200)*ClassicalSixthBranch.v ((614216077:ℝ)/168755200)/ClassicalSixthBranch.r = (125908880254137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1513
  · change upperPayment 1514 ≤ upperValue ((point split endpoint 4096 1514+point split endpoint 4096 1515)/2)
    have hp : upperPayment 1514 = (318861996538:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1514+point split endpoint 4096 1515)/2 = (614241227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614241227:ℝ)/168755200)*ClassicalSixthBranch.v ((614241227:ℝ)/168755200)/ClassicalSixthBranch.r = (125885927382281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1514
  · change upperPayment 1515 ≤ upperValue ((point split endpoint 4096 1515+point split endpoint 4096 1516)/2)
    have hp : upperPayment 1515 = (318775625221:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1515+point split endpoint 4096 1516)/2 = (614266377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614266377:ℝ)/168755200)*ClassicalSixthBranch.v ((614266377:ℝ)/168755200)/ClassicalSixthBranch.r = (125862976534497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1515
  · change upperPayment 1516 ≤ upperValue ((point split endpoint 4096 1516+point split endpoint 4096 1517)/2)
    have hp : upperPayment 1516 = (318689229962:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1516+point split endpoint 4096 1517)/2 = (614291527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614291527:ℝ)/168755200)*ClassicalSixthBranch.v ((614291527:ℝ)/168755200)/ClassicalSixthBranch.r = (125840027710785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1516
  · change upperPayment 1517 ≤ upperValue ((point split endpoint 4096 1517+point split endpoint 4096 1518)/2)
    have hp : upperPayment 1517 = (318602810756:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1517+point split endpoint 4096 1518)/2 = (614316677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614316677:ℝ)/168755200)*ClassicalSixthBranch.v ((614316677:ℝ)/168755200)/ClassicalSixthBranch.r = (125817080911145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1517
  · change upperPayment 1518 ≤ upperValue ((point split endpoint 4096 1518+point split endpoint 4096 1519)/2)
    have hp : upperPayment 1518 = (318516367599:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1518+point split endpoint 4096 1519)/2 = (614341827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614341827:ℝ)/168755200)*ClassicalSixthBranch.v ((614341827:ℝ)/168755200)/ClassicalSixthBranch.r = (125794136135577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1518
  · change upperPayment 1519 ≤ upperValue ((point split endpoint 4096 1519+point split endpoint 4096 1520)/2)
    have hp : upperPayment 1519 = (318429900486:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1519+point split endpoint 4096 1520)/2 = (614366977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((614366977:ℝ)/168755200)*ClassicalSixthBranch.v ((614366977:ℝ)/168755200)/ClassicalSixthBranch.r = (125771193384081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1519
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_094
