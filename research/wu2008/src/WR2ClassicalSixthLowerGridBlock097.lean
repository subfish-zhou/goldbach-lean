import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints097
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_097 (j : Fin 16) : lowerPayment (16*97+j.val) ≤
    lowerValue ((point 2 split 4096 (16*97+j.val)+point 2 split 4096 (16*97+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1552 ≤ lowerValue ((point 2 split 4096 1552+point 2 split 4096 1553)/2)
    have hp : lowerPayment 1552 = (190627258776:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1552+point 2 split 4096 1553)/2 = (85592431:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85592431:ℝ)/33751040)/ClassicalSixthBranch.v ((85592431:ℝ)/33751040) = (693985697819:ℝ)/346046213528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1552
  · change lowerPayment 1553 ≤ lowerValue ((point 2 split 4096 1553+point 2 split 4096 1554)/2)
    have hp : lowerPayment 1553 = (190724675640:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1553+point 2 split 4096 1554)/2 = (428020417:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428020417:ℝ)/168755200)/ClassicalSixthBranch.v ((428020417:ℝ)/168755200) = (138781676829:ℝ)/69199641128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1553
  · change lowerPayment 1554 ≤ lowerValue ((point 2 split 4096 1554+point 2 split 4096 1555)/2)
    have hp : lowerPayment 1554 = (190822074055:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1554+point 2 split 4096 1555)/2 = (428078679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428078679:ℝ)/168755200)/ClassicalSixthBranch.v ((428078679:ℝ)/168755200) = (693831070471:ℝ)/345950197752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1554
  · change lowerPayment 1555 ≤ lowerValue ((point 2 split 4096 1555+point 2 split 4096 1556)/2)
    have hp : lowerPayment 1555 = (190919454041:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1555+point 2 split 4096 1556)/2 = (428136941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428136941:ℝ)/168755200)/ClassicalSixthBranch.v ((428136941:ℝ)/168755200) = (693753756797:ℝ)/345902189864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1555
  · change lowerPayment 1556 ≤ lowerValue ((point 2 split 4096 1556+point 2 split 4096 1557)/2)
    have hp : lowerPayment 1556 = (191016815619:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1556+point 2 split 4096 1557)/2 = (428195203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428195203:ℝ)/168755200)/ClassicalSixthBranch.v ((428195203:ℝ)/168755200) = (693676443123:ℝ)/345854181976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1556
  · change lowerPayment 1557 ≤ lowerValue ((point 2 split 4096 1557+point 2 split 4096 1558)/2)
    have hp : lowerPayment 1557 = (191114158810:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1557+point 2 split 4096 1558)/2 = (85650693:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85650693:ℝ)/33751040)/ClassicalSixthBranch.v ((85650693:ℝ)/33751040) = (693599129449:ℝ)/345806174088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1557
  · change lowerPayment 1558 ≤ lowerValue ((point 2 split 4096 1558+point 2 split 4096 1559)/2)
    have hp : lowerPayment 1558 = (191211483634:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1558+point 2 split 4096 1559)/2 = (428311727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428311727:ℝ)/168755200)/ClassicalSixthBranch.v ((428311727:ℝ)/168755200) = (27740872631:ℝ)/13830326648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1558
  · change lowerPayment 1559 ≤ lowerValue ((point 2 split 4096 1559+point 2 split 4096 1560)/2)
    have hp : lowerPayment 1559 = (191308790112:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1559+point 2 split 4096 1560)/2 = (428369989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428369989:ℝ)/168755200)/ClassicalSixthBranch.v ((428369989:ℝ)/168755200) = (693444502101:ℝ)/345710158312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1559
  · change lowerPayment 1560 ≤ lowerValue ((point 2 split 4096 1560+point 2 split 4096 1561)/2)
    have hp : lowerPayment 1560 = (191406078265:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1560+point 2 split 4096 1561)/2 = (428428251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428428251:ℝ)/168755200)/ClassicalSixthBranch.v ((428428251:ℝ)/168755200) = (693367188427:ℝ)/345662150424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1560
  · change lowerPayment 1561 ≤ lowerValue ((point 2 split 4096 1561+point 2 split 4096 1562)/2)
    have hp : lowerPayment 1561 = (191503348113:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1561+point 2 split 4096 1562)/2 = (428486513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428486513:ℝ)/168755200)/ClassicalSixthBranch.v ((428486513:ℝ)/168755200) = (693289874753:ℝ)/345614142536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1561
  · change lowerPayment 1562 ≤ lowerValue ((point 2 split 4096 1562+point 2 split 4096 1563)/2)
    have hp : lowerPayment 1562 = (191600599676:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1562+point 2 split 4096 1563)/2 = (17141791:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17141791:ℝ)/6750208)/ClassicalSixthBranch.v ((17141791:ℝ)/6750208) = (693212561079:ℝ)/345566134648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1562
  · change lowerPayment 1563 ≤ lowerValue ((point 2 split 4096 1563+point 2 split 4096 1564)/2)
    have hp : lowerPayment 1563 = (191697832976:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1563+point 2 split 4096 1564)/2 = (428603037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428603037:ℝ)/168755200)/ClassicalSixthBranch.v ((428603037:ℝ)/168755200) = (138627049481:ℝ)/69103625352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1563
  · change lowerPayment 1564 ≤ lowerValue ((point 2 split 4096 1564+point 2 split 4096 1565)/2)
    have hp : lowerPayment 1564 = (191795048032:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1564+point 2 split 4096 1565)/2 = (428661299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428661299:ℝ)/168755200)/ClassicalSixthBranch.v ((428661299:ℝ)/168755200) = (693057933731:ℝ)/345470118872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1564
  · change lowerPayment 1565 ≤ lowerValue ((point 2 split 4096 1565+point 2 split 4096 1566)/2)
    have hp : lowerPayment 1565 = (191892244866:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1565+point 2 split 4096 1566)/2 = (428719561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428719561:ℝ)/168755200)/ClassicalSixthBranch.v ((428719561:ℝ)/168755200) = (692980620057:ℝ)/345422110984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1565
  · change lowerPayment 1566 ≤ lowerValue ((point 2 split 4096 1566+point 2 split 4096 1567)/2)
    have hp : lowerPayment 1566 = (191989423498:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1566+point 2 split 4096 1567)/2 = (428777823:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428777823:ℝ)/168755200)/ClassicalSixthBranch.v ((428777823:ℝ)/168755200) = (692903306383:ℝ)/345374103096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1566
  · change lowerPayment 1567 ≤ lowerValue ((point 2 split 4096 1567+point 2 split 4096 1568)/2)
    have hp : lowerPayment 1567 = (192086583948:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1567+point 2 split 4096 1568)/2 = (85767217:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85767217:ℝ)/33751040)/ClassicalSixthBranch.v ((85767217:ℝ)/33751040) = (692825992709:ℝ)/345326095208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1567
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_097
