import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints091
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_091 (j : Fin 16) : lowerPayment (16*91+j.val) ≤
    lowerValue ((point 2 split 4096 (16*91+j.val)+point 2 split 4096 (16*91+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1456 ≤ lowerValue ((point 2 split 4096 1456+point 2 split 4096 1457)/2)
    have hp : lowerPayment 1456 = (181186154553:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1456+point 2 split 4096 1457)/2 = (422369003:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422369003:ℝ)/168755200)/ClassicalSixthBranch.v ((422369003:ℝ)/168755200) = (701407810523:ℝ)/350654970776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1456
  · change lowerPayment 1457 ≤ lowerValue ((point 2 split 4096 1457+point 2 split 4096 1458)/2)
    have hp : lowerPayment 1457 = (181285440509:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1457+point 2 split 4096 1458)/2 = (84485453:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84485453:ℝ)/33751040)/ClassicalSixthBranch.v ((84485453:ℝ)/33751040) = (701330496849:ℝ)/350606962888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1457
  · change lowerPayment 1458 ≤ lowerValue ((point 2 split 4096 1458+point 2 split 4096 1459)/2)
    have hp : lowerPayment 1458 = (181384705977:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1458+point 2 split 4096 1459)/2 = (422485527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422485527:ℝ)/168755200)/ClassicalSixthBranch.v ((422485527:ℝ)/168755200) = (28050127327:ℝ)/14022358200 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1458
  · change lowerPayment 1459 ≤ lowerValue ((point 2 split 4096 1459+point 2 split 4096 1460)/2)
    have hp : lowerPayment 1459 = (181483950979:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1459+point 2 split 4096 1460)/2 = (422543789:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422543789:ℝ)/168755200)/ClassicalSixthBranch.v ((422543789:ℝ)/168755200) = (701175869501:ℝ)/350510947112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1459
  · change lowerPayment 1460 ≤ lowerValue ((point 2 split 4096 1460+point 2 split 4096 1461)/2)
    have hp : lowerPayment 1460 = (181583175538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1460+point 2 split 4096 1461)/2 = (422602051:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422602051:ℝ)/168755200)/ClassicalSixthBranch.v ((422602051:ℝ)/168755200) = (701098555827:ℝ)/350462939224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1460
  · change lowerPayment 1461 ≤ lowerValue ((point 2 split 4096 1461+point 2 split 4096 1462)/2)
    have hp : lowerPayment 1461 = (181682379673:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1461+point 2 split 4096 1462)/2 = (422660313:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422660313:ℝ)/168755200)/ClassicalSixthBranch.v ((422660313:ℝ)/168755200) = (701021242153:ℝ)/350414931336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1461
  · change lowerPayment 1462 ≤ lowerValue ((point 2 split 4096 1462+point 2 split 4096 1463)/2)
    have hp : lowerPayment 1462 = (181781563409:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1462+point 2 split 4096 1463)/2 = (16908743:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16908743:ℝ)/6750208)/ClassicalSixthBranch.v ((16908743:ℝ)/6750208) = (700943928479:ℝ)/350366923448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1462
  · change lowerPayment 1463 ≤ lowerValue ((point 2 split 4096 1463+point 2 split 4096 1464)/2)
    have hp : lowerPayment 1463 = (181880726765:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1463+point 2 split 4096 1464)/2 = (422776837:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422776837:ℝ)/168755200)/ClassicalSixthBranch.v ((422776837:ℝ)/168755200) = (140173322961:ℝ)/70063783112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1463
  · change lowerPayment 1464 ≤ lowerValue ((point 2 split 4096 1464+point 2 split 4096 1465)/2)
    have hp : lowerPayment 1464 = (181979869765:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1464+point 2 split 4096 1465)/2 = (422835099:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422835099:ℝ)/168755200)/ClassicalSixthBranch.v ((422835099:ℝ)/168755200) = (700789301131:ℝ)/350270907672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1464
  · change lowerPayment 1465 ≤ lowerValue ((point 2 split 4096 1465+point 2 split 4096 1466)/2)
    have hp : lowerPayment 1465 = (182078992430:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1465+point 2 split 4096 1466)/2 = (422893361:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422893361:ℝ)/168755200)/ClassicalSixthBranch.v ((422893361:ℝ)/168755200) = (700711987457:ℝ)/350222899784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1465
  · change lowerPayment 1466 ≤ lowerValue ((point 2 split 4096 1466+point 2 split 4096 1467)/2)
    have hp : lowerPayment 1466 = (182178094781:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1466+point 2 split 4096 1467)/2 = (422951623:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422951623:ℝ)/168755200)/ClassicalSixthBranch.v ((422951623:ℝ)/168755200) = (700634673783:ℝ)/350174891896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1466
  · change lowerPayment 1467 ≤ lowerValue ((point 2 split 4096 1467+point 2 split 4096 1468)/2)
    have hp : lowerPayment 1467 = (182277176840:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1467+point 2 split 4096 1468)/2 = (84601977:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84601977:ℝ)/33751040)/ClassicalSixthBranch.v ((84601977:ℝ)/33751040) = (700557360109:ℝ)/350126884008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1467
  · change lowerPayment 1468 ≤ lowerValue ((point 2 split 4096 1468+point 2 split 4096 1469)/2)
    have hp : lowerPayment 1468 = (182376238629:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1468+point 2 split 4096 1469)/2 = (423068147:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423068147:ℝ)/168755200)/ClassicalSixthBranch.v ((423068147:ℝ)/168755200) = (140096009287:ℝ)/70015775224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1468
  · change lowerPayment 1469 ≤ lowerValue ((point 2 split 4096 1469+point 2 split 4096 1470)/2)
    have hp : lowerPayment 1469 = (182475280170:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1469+point 2 split 4096 1470)/2 = (423126409:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423126409:ℝ)/168755200)/ClassicalSixthBranch.v ((423126409:ℝ)/168755200) = (700402732761:ℝ)/350030868232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1469
  · change lowerPayment 1470 ≤ lowerValue ((point 2 split 4096 1470+point 2 split 4096 1471)/2)
    have hp : lowerPayment 1470 = (182574301485:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1470+point 2 split 4096 1471)/2 = (423184671:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423184671:ℝ)/168755200)/ClassicalSixthBranch.v ((423184671:ℝ)/168755200) = (700325419087:ℝ)/349982860344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1470
  · change lowerPayment 1471 ≤ lowerValue ((point 2 split 4096 1471+point 2 split 4096 1472)/2)
    have hp : lowerPayment 1471 = (182673302594:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1471+point 2 split 4096 1472)/2 = (423242933:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((423242933:ℝ)/168755200)/ClassicalSixthBranch.v ((423242933:ℝ)/168755200) = (700248105413:ℝ)/349934852456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1471
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_091
