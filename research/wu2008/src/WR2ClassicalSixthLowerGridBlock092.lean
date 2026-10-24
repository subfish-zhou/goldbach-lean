import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints092
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_092 (j : Fin 16) : lowerPayment (16*92+j.val) ≤
    lowerValue ((point 2 split 4096 (16*92+j.val)+point 2 split 4096 (16*92+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1472 ≤ lowerValue ((point 2 split 4096 1472+point 2 split 4096 1473)/2)
    have hp : lowerPayment 1472 = (182772283520:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1472+point 2 split 4096 1473)/2 = (84660239:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84660239:ℝ)/33751040)/ClassicalSixthBranch.v ((84660239:ℝ)/33751040) = (700170791739:ℝ)/349886844568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1472
  · change lowerPayment 1473 ≤ lowerValue ((point 2 split 4096 1473+point 2 split 4096 1474)/2)
    have hp : lowerPayment 1473 = (182871244284:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1473+point 2 split 4096 1474)/2 = (423359457:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423359457:ℝ)/168755200)/ClassicalSixthBranch.v ((423359457:ℝ)/168755200) = (140018695613:ℝ)/69967767336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1473
  · change lowerPayment 1474 ≤ lowerValue ((point 2 split 4096 1474+point 2 split 4096 1475)/2)
    have hp : lowerPayment 1474 = (182970184908:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1474+point 2 split 4096 1475)/2 = (423417719:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423417719:ℝ)/168755200)/ClassicalSixthBranch.v ((423417719:ℝ)/168755200) = (700016164391:ℝ)/349790828792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1474
  · change lowerPayment 1475 ≤ lowerValue ((point 2 split 4096 1475+point 2 split 4096 1476)/2)
    have hp : lowerPayment 1475 = (183069105414:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1475+point 2 split 4096 1476)/2 = (423475981:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423475981:ℝ)/168755200)/ClassicalSixthBranch.v ((423475981:ℝ)/168755200) = (699938850717:ℝ)/349742820904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1475
  · change lowerPayment 1476 ≤ lowerValue ((point 2 split 4096 1476+point 2 split 4096 1477)/2)
    have hp : lowerPayment 1476 = (183168005823:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1476+point 2 split 4096 1477)/2 = (423534243:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423534243:ℝ)/168755200)/ClassicalSixthBranch.v ((423534243:ℝ)/168755200) = (699861537043:ℝ)/349694813016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1476
  · change lowerPayment 1477 ≤ lowerValue ((point 2 split 4096 1477+point 2 split 4096 1478)/2)
    have hp : lowerPayment 1477 = (183266886157:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1477+point 2 split 4096 1478)/2 = (84718501:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84718501:ℝ)/33751040)/ClassicalSixthBranch.v ((84718501:ℝ)/33751040) = (699784223369:ℝ)/349646805128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1477
  · change lowerPayment 1478 ≤ lowerValue ((point 2 split 4096 1478+point 2 split 4096 1479)/2)
    have hp : lowerPayment 1478 = (183365746437:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1478+point 2 split 4096 1479)/2 = (423650767:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423650767:ℝ)/168755200)/ClassicalSixthBranch.v ((423650767:ℝ)/168755200) = (139941381939:ℝ)/69919759448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1478
  · change lowerPayment 1479 ≤ lowerValue ((point 2 split 4096 1479+point 2 split 4096 1480)/2)
    have hp : lowerPayment 1479 = (183464586685:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1479+point 2 split 4096 1480)/2 = (423709029:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423709029:ℝ)/168755200)/ClassicalSixthBranch.v ((423709029:ℝ)/168755200) = (699629596021:ℝ)/349550789352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1479
  · change lowerPayment 1480 ≤ lowerValue ((point 2 split 4096 1480+point 2 split 4096 1481)/2)
    have hp : lowerPayment 1480 = (183563406923:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1480+point 2 split 4096 1481)/2 = (423767291:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423767291:ℝ)/168755200)/ClassicalSixthBranch.v ((423767291:ℝ)/168755200) = (699552282347:ℝ)/349502781464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1480
  · change lowerPayment 1481 ≤ lowerValue ((point 2 split 4096 1481+point 2 split 4096 1482)/2)
    have hp : lowerPayment 1481 = (183662207171:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1481+point 2 split 4096 1482)/2 = (423825553:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423825553:ℝ)/168755200)/ClassicalSixthBranch.v ((423825553:ℝ)/168755200) = (699474968673:ℝ)/349454773576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1481
  · change lowerPayment 1482 ≤ lowerValue ((point 2 split 4096 1482+point 2 split 4096 1483)/2)
    have hp : lowerPayment 1482 = (183760987453:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1482+point 2 split 4096 1483)/2 = (84776763:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84776763:ℝ)/33751040)/ClassicalSixthBranch.v ((84776763:ℝ)/33751040) = (699397654999:ℝ)/349406765688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1482
  · change lowerPayment 1483 ≤ lowerValue ((point 2 split 4096 1483+point 2 split 4096 1484)/2)
    have hp : lowerPayment 1483 = (183859747788:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1483+point 2 split 4096 1484)/2 = (423942077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423942077:ℝ)/168755200)/ClassicalSixthBranch.v ((423942077:ℝ)/168755200) = (27972813653:ℝ)/13974350312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1483
  · change lowerPayment 1484 ≤ lowerValue ((point 2 split 4096 1484+point 2 split 4096 1485)/2)
    have hp : lowerPayment 1484 = (183958488199:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1484+point 2 split 4096 1485)/2 = (424000339:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424000339:ℝ)/168755200)/ClassicalSixthBranch.v ((424000339:ℝ)/168755200) = (699243027651:ℝ)/349310749912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1484
  · change lowerPayment 1485 ≤ lowerValue ((point 2 split 4096 1485+point 2 split 4096 1486)/2)
    have hp : lowerPayment 1485 = (184057208707:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1485+point 2 split 4096 1486)/2 = (424058601:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424058601:ℝ)/168755200)/ClassicalSixthBranch.v ((424058601:ℝ)/168755200) = (699165713977:ℝ)/349262742024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1485
  · change lowerPayment 1486 ≤ lowerValue ((point 2 split 4096 1486+point 2 split 4096 1487)/2)
    have hp : lowerPayment 1486 = (184155909333:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1486+point 2 split 4096 1487)/2 = (424116863:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424116863:ℝ)/168755200)/ClassicalSixthBranch.v ((424116863:ℝ)/168755200) = (699088400303:ℝ)/349214734136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1486
  · change lowerPayment 1487 ≤ lowerValue ((point 2 split 4096 1487+point 2 split 4096 1488)/2)
    have hp : lowerPayment 1487 = (184254590100:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1487+point 2 split 4096 1488)/2 = (16967005:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16967005:ℝ)/6750208)/ClassicalSixthBranch.v ((16967005:ℝ)/6750208) = (699011086629:ℝ)/349166726248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1487
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_092
