import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints098
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_098 (j : Fin 16) : lowerPayment (16*98+j.val) ≤
    lowerValue ((point 2 split 4096 (16*98+j.val)+point 2 split 4096 (16*98+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1568 ≤ lowerValue ((point 2 split 4096 1568+point 2 split 4096 1569)/2)
    have hp : lowerPayment 1568 = (192183726237:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1568+point 2 split 4096 1569)/2 = (428894347:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428894347:ℝ)/168755200)/ClassicalSixthBranch.v ((428894347:ℝ)/168755200) = (138549735807:ℝ)/69055617464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1568
  · change lowerPayment 1569 ≤ lowerValue ((point 2 split 4096 1569+point 2 split 4096 1570)/2)
    have hp : lowerPayment 1569 = (192280850385:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1569+point 2 split 4096 1570)/2 = (428952609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((428952609:ℝ)/168755200)/ClassicalSixthBranch.v ((428952609:ℝ)/168755200) = (692671365361:ℝ)/345230079432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1569
  · change lowerPayment 1570 ≤ lowerValue ((point 2 split 4096 1570+point 2 split 4096 1571)/2)
    have hp : lowerPayment 1570 = (192377956413:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1570+point 2 split 4096 1571)/2 = (429010871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429010871:ℝ)/168755200)/ClassicalSixthBranch.v ((429010871:ℝ)/168755200) = (692594051687:ℝ)/345182071544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1570
  · change lowerPayment 1571 ≤ lowerValue ((point 2 split 4096 1571+point 2 split 4096 1572)/2)
    have hp : lowerPayment 1571 = (192475044342:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1571+point 2 split 4096 1572)/2 = (429069133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429069133:ℝ)/168755200)/ClassicalSixthBranch.v ((429069133:ℝ)/168755200) = (692516738013:ℝ)/345134063656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1571
  · change lowerPayment 1572 ≤ lowerValue ((point 2 split 4096 1572+point 2 split 4096 1573)/2)
    have hp : lowerPayment 1572 = (192572114191:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1572+point 2 split 4096 1573)/2 = (85825479:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85825479:ℝ)/33751040)/ClassicalSixthBranch.v ((85825479:ℝ)/33751040) = (692439424339:ℝ)/345086055768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1572
  · change lowerPayment 1573 ≤ lowerValue ((point 2 split 4096 1573+point 2 split 4096 1574)/2)
    have hp : lowerPayment 1573 = (192669165982:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1573+point 2 split 4096 1574)/2 = (429185657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429185657:ℝ)/168755200)/ClassicalSixthBranch.v ((429185657:ℝ)/168755200) = (138472422133:ℝ)/69007609576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1573
  · change lowerPayment 1574 ≤ lowerValue ((point 2 split 4096 1574+point 2 split 4096 1575)/2)
    have hp : lowerPayment 1574 = (192766199734:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1574+point 2 split 4096 1575)/2 = (429243919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429243919:ℝ)/168755200)/ClassicalSixthBranch.v ((429243919:ℝ)/168755200) = (692284796991:ℝ)/344990039992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1574
  · change lowerPayment 1575 ≤ lowerValue ((point 2 split 4096 1575+point 2 split 4096 1576)/2)
    have hp : lowerPayment 1575 = (192863215468:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1575+point 2 split 4096 1576)/2 = (429302181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429302181:ℝ)/168755200)/ClassicalSixthBranch.v ((429302181:ℝ)/168755200) = (692207483317:ℝ)/344942032104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1575
  · change lowerPayment 1576 ≤ lowerValue ((point 2 split 4096 1576+point 2 split 4096 1577)/2)
    have hp : lowerPayment 1576 = (192960213205:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1576+point 2 split 4096 1577)/2 = (429360443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429360443:ℝ)/168755200)/ClassicalSixthBranch.v ((429360443:ℝ)/168755200) = (692130169643:ℝ)/344894024216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1576
  · change lowerPayment 1577 ≤ lowerValue ((point 2 split 4096 1577+point 2 split 4096 1578)/2)
    have hp : lowerPayment 1577 = (193057192965:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1577+point 2 split 4096 1578)/2 = (85883741:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85883741:ℝ)/33751040)/ClassicalSixthBranch.v ((85883741:ℝ)/33751040) = (692052855969:ℝ)/344846016328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1577
  · change lowerPayment 1578 ≤ lowerValue ((point 2 split 4096 1578+point 2 split 4096 1579)/2)
    have hp : lowerPayment 1578 = (193154154768:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1578+point 2 split 4096 1579)/2 = (429476967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429476967:ℝ)/168755200)/ClassicalSixthBranch.v ((429476967:ℝ)/168755200) = (138395108459:ℝ)/68959601688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1578
  · change lowerPayment 1579 ≤ lowerValue ((point 2 split 4096 1579+point 2 split 4096 1580)/2)
    have hp : lowerPayment 1579 = (193251098634:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1579+point 2 split 4096 1580)/2 = (429535229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429535229:ℝ)/168755200)/ClassicalSixthBranch.v ((429535229:ℝ)/168755200) = (691898228621:ℝ)/344750000552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1579
  · change lowerPayment 1580 ≤ lowerValue ((point 2 split 4096 1580+point 2 split 4096 1581)/2)
    have hp : lowerPayment 1580 = (193348024585:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1580+point 2 split 4096 1581)/2 = (429593491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429593491:ℝ)/168755200)/ClassicalSixthBranch.v ((429593491:ℝ)/168755200) = (691820914947:ℝ)/344701992664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1580
  · change lowerPayment 1581 ≤ lowerValue ((point 2 split 4096 1581+point 2 split 4096 1582)/2)
    have hp : lowerPayment 1581 = (193444932640:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1581+point 2 split 4096 1582)/2 = (429651753:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429651753:ℝ)/168755200)/ClassicalSixthBranch.v ((429651753:ℝ)/168755200) = (691743601273:ℝ)/344653984776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1581
  · change lowerPayment 1582 ≤ lowerValue ((point 2 split 4096 1582+point 2 split 4096 1583)/2)
    have hp : lowerPayment 1582 = (193541822820:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1582+point 2 split 4096 1583)/2 = (85942003:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85942003:ℝ)/33751040)/ClassicalSixthBranch.v ((85942003:ℝ)/33751040) = (691666287599:ℝ)/344605976888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1582
  · change lowerPayment 1583 ≤ lowerValue ((point 2 split 4096 1583+point 2 split 4096 1584)/2)
    have hp : lowerPayment 1583 = (193638695145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1583+point 2 split 4096 1584)/2 = (429768277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429768277:ℝ)/168755200)/ClassicalSixthBranch.v ((429768277:ℝ)/168755200) = (27663558957:ℝ)/13782318760 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1583
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_098
