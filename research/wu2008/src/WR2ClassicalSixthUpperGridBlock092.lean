import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints092
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_092 (j : Fin 16) : upperPayment (16*92+j.val) ≤
    upperValue ((point split endpoint 4096 (16*92+j.val)+point split endpoint 4096 (16*92+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1472 ≤ upperValue ((point split endpoint 4096 1472+point split endpoint 4096 1473)/2)
    have hp : upperPayment 1472 = (322468027628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1472+point split endpoint 4096 1473)/2 = (613184927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613184927:ℝ)/168755200)*ClassicalSixthBranch.v ((613184927:ℝ)/168755200)/ClassicalSixthBranch.r = (126851690726225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1472
  · change upperPayment 1473 ≤ upperValue ((point split endpoint 4096 1473+point split endpoint 4096 1474)/2)
    have hp : upperPayment 1473 = (322382658090:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1473+point split endpoint 4096 1474)/2 = (613210077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613210077:ℝ)/168755200)*ClassicalSixthBranch.v ((613210077:ℝ)/168755200)/ClassicalSixthBranch.r = (126828654867417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1473
  · change upperPayment 1474 ≤ upperValue ((point split endpoint 4096 1474+point split endpoint 4096 1475)/2)
    have hp : upperPayment 1474 = (322297264786:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1474+point split endpoint 4096 1475)/2 = (613235227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613235227:ℝ)/168755200)*ClassicalSixthBranch.v ((613235227:ℝ)/168755200)/ClassicalSixthBranch.r = (126805621032681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1474
  · change upperPayment 1475 ≤ upperValue ((point split endpoint 4096 1475+point split endpoint 4096 1476)/2)
    have hp : upperPayment 1475 = (322211847713:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1475+point split endpoint 4096 1476)/2 = (613260377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613260377:ℝ)/168755200)*ClassicalSixthBranch.v ((613260377:ℝ)/168755200)/ClassicalSixthBranch.r = (126782589222017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1475
  · change upperPayment 1476 ≤ upperValue ((point split endpoint 4096 1476+point split endpoint 4096 1477)/2)
    have hp : upperPayment 1476 = (322126406865:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1476+point split endpoint 4096 1477)/2 = (613285527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613285527:ℝ)/168755200)*ClassicalSixthBranch.v ((613285527:ℝ)/168755200)/ClassicalSixthBranch.r = (126759559435425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1476
  · change upperPayment 1477 ≤ upperValue ((point split endpoint 4096 1477+point split endpoint 4096 1478)/2)
    have hp : upperPayment 1477 = (322040942238:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1477+point split endpoint 4096 1478)/2 = (613310677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613310677:ℝ)/168755200)*ClassicalSixthBranch.v ((613310677:ℝ)/168755200)/ClassicalSixthBranch.r = (126736531672905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1477
  · change upperPayment 1478 ≤ upperValue ((point split endpoint 4096 1478+point split endpoint 4096 1479)/2)
    have hp : upperPayment 1478 = (321955453829:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1478+point split endpoint 4096 1479)/2 = (613335827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613335827:ℝ)/168755200)*ClassicalSixthBranch.v ((613335827:ℝ)/168755200)/ClassicalSixthBranch.r = (126713505934457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1478
  · change upperPayment 1479 ≤ upperValue ((point split endpoint 4096 1479+point split endpoint 4096 1480)/2)
    have hp : upperPayment 1479 = (321869941634:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1479+point split endpoint 4096 1480)/2 = (613360977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613360977:ℝ)/168755200)*ClassicalSixthBranch.v ((613360977:ℝ)/168755200)/ClassicalSixthBranch.r = (126690482220081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1479
  · change upperPayment 1480 ≤ upperValue ((point split endpoint 4096 1480+point split endpoint 4096 1481)/2)
    have hp : upperPayment 1480 = (321784405647:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1480+point split endpoint 4096 1481)/2 = (613386127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613386127:ℝ)/168755200)*ClassicalSixthBranch.v ((613386127:ℝ)/168755200)/ClassicalSixthBranch.r = (126667460529777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1480
  · change upperPayment 1481 ≤ upperValue ((point split endpoint 4096 1481+point split endpoint 4096 1482)/2)
    have hp : upperPayment 1481 = (321698845866:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1481+point split endpoint 4096 1482)/2 = (613411277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613411277:ℝ)/168755200)*ClassicalSixthBranch.v ((613411277:ℝ)/168755200)/ClassicalSixthBranch.r = (126644440863545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1481
  · change upperPayment 1482 ≤ upperValue ((point split endpoint 4096 1482+point split endpoint 4096 1483)/2)
    have hp : upperPayment 1482 = (321613262285:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1482+point split endpoint 4096 1483)/2 = (613436427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613436427:ℝ)/168755200)*ClassicalSixthBranch.v ((613436427:ℝ)/168755200)/ClassicalSixthBranch.r = (126621423221385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1482
  · change upperPayment 1483 ≤ upperValue ((point split endpoint 4096 1483+point split endpoint 4096 1484)/2)
    have hp : upperPayment 1483 = (321527654900:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1483+point split endpoint 4096 1484)/2 = (613461577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613461577:ℝ)/168755200)*ClassicalSixthBranch.v ((613461577:ℝ)/168755200)/ClassicalSixthBranch.r = (126598407603297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1483
  · change upperPayment 1484 ≤ upperValue ((point split endpoint 4096 1484+point split endpoint 4096 1485)/2)
    have hp : upperPayment 1484 = (321442023708:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1484+point split endpoint 4096 1485)/2 = (613486727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613486727:ℝ)/168755200)*ClassicalSixthBranch.v ((613486727:ℝ)/168755200)/ClassicalSixthBranch.r = (126575394009281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1484
  · change upperPayment 1485 ≤ upperValue ((point split endpoint 4096 1485+point split endpoint 4096 1486)/2)
    have hp : upperPayment 1485 = (321356368704:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1485+point split endpoint 4096 1486)/2 = (613511877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613511877:ℝ)/168755200)*ClassicalSixthBranch.v ((613511877:ℝ)/168755200)/ClassicalSixthBranch.r = (126552382439337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1485
  · change upperPayment 1486 ≤ upperValue ((point split endpoint 4096 1486+point split endpoint 4096 1487)/2)
    have hp : upperPayment 1486 = (321270689884:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1486+point split endpoint 4096 1487)/2 = (613537027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613537027:ℝ)/168755200)*ClassicalSixthBranch.v ((613537027:ℝ)/168755200)/ClassicalSixthBranch.r = (126529372893465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1486
  · change upperPayment 1487 ≤ upperValue ((point split endpoint 4096 1487+point split endpoint 4096 1488)/2)
    have hp : upperPayment 1487 = (321184987244:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1487+point split endpoint 4096 1488)/2 = (613562177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613562177:ℝ)/168755200)*ClassicalSixthBranch.v ((613562177:ℝ)/168755200)/ClassicalSixthBranch.r = (126506365371665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1487
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_092
