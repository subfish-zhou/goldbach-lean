import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints099
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_099 (j : Fin 16) : lowerPayment (16*99+j.val) ≤
    lowerValue ((point 2 split 4096 (16*99+j.val)+point 2 split 4096 (16*99+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1584 ≤ lowerValue ((point 2 split 4096 1584+point 2 split 4096 1585)/2)
    have hp : lowerPayment 1584 = (193735549636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1584+point 2 split 4096 1585)/2 = (429826539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429826539:ℝ)/168755200)/ClassicalSixthBranch.v ((429826539:ℝ)/168755200) = (691511660251:ℝ)/344509961112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1584
  · change lowerPayment 1585 ≤ lowerValue ((point 2 split 4096 1585+point 2 split 4096 1586)/2)
    have hp : lowerPayment 1585 = (193832386312:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1585+point 2 split 4096 1586)/2 = (429884801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429884801:ℝ)/168755200)/ClassicalSixthBranch.v ((429884801:ℝ)/168755200) = (691434346577:ℝ)/344461953224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1585
  · change lowerPayment 1586 ≤ lowerValue ((point 2 split 4096 1586+point 2 split 4096 1587)/2)
    have hp : lowerPayment 1586 = (193929205194:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1586+point 2 split 4096 1587)/2 = (429943063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((429943063:ℝ)/168755200)/ClassicalSixthBranch.v ((429943063:ℝ)/168755200) = (691357032903:ℝ)/344413945336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1586
  · change lowerPayment 1587 ≤ lowerValue ((point 2 split 4096 1587+point 2 split 4096 1588)/2)
    have hp : lowerPayment 1587 = (194026006303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1587+point 2 split 4096 1588)/2 = (17200053:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17200053:ℝ)/6750208)/ClassicalSixthBranch.v ((17200053:ℝ)/6750208) = (691279719229:ℝ)/344365937448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1587
  · change lowerPayment 1588 ≤ lowerValue ((point 2 split 4096 1588+point 2 split 4096 1589)/2)
    have hp : lowerPayment 1588 = (194122789658:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1588+point 2 split 4096 1589)/2 = (430059587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430059587:ℝ)/168755200)/ClassicalSixthBranch.v ((430059587:ℝ)/168755200) = (138240481111:ℝ)/68863585912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1588
  · change lowerPayment 1589 ≤ lowerValue ((point 2 split 4096 1589+point 2 split 4096 1590)/2)
    have hp : lowerPayment 1589 = (194219555280:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1589+point 2 split 4096 1590)/2 = (430117849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430117849:ℝ)/168755200)/ClassicalSixthBranch.v ((430117849:ℝ)/168755200) = (691125091881:ℝ)/344269921672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1589
  · change lowerPayment 1590 ≤ lowerValue ((point 2 split 4096 1590+point 2 split 4096 1591)/2)
    have hp : lowerPayment 1590 = (194316303189:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1590+point 2 split 4096 1591)/2 = (430176111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430176111:ℝ)/168755200)/ClassicalSixthBranch.v ((430176111:ℝ)/168755200) = (691047778207:ℝ)/344221913784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1590
  · change lowerPayment 1591 ≤ lowerValue ((point 2 split 4096 1591+point 2 split 4096 1592)/2)
    have hp : lowerPayment 1591 = (194413033406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1591+point 2 split 4096 1592)/2 = (430234373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430234373:ℝ)/168755200)/ClassicalSixthBranch.v ((430234373:ℝ)/168755200) = (690970464533:ℝ)/344173905896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1591
  · change lowerPayment 1592 ≤ lowerValue ((point 2 split 4096 1592+point 2 split 4096 1593)/2)
    have hp : lowerPayment 1592 = (194509745950:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1592+point 2 split 4096 1593)/2 = (86058527:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86058527:ℝ)/33751040)/ClassicalSixthBranch.v ((86058527:ℝ)/33751040) = (690893150859:ℝ)/344125898008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1592
  · change lowerPayment 1593 ≤ lowerValue ((point 2 split 4096 1593+point 2 split 4096 1594)/2)
    have hp : lowerPayment 1593 = (194606440842:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1593+point 2 split 4096 1594)/2 = (430350897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430350897:ℝ)/168755200)/ClassicalSixthBranch.v ((430350897:ℝ)/168755200) = (138163167437:ℝ)/68815578024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1593
  · change lowerPayment 1594 ≤ lowerValue ((point 2 split 4096 1594+point 2 split 4096 1595)/2)
    have hp : lowerPayment 1594 = (194703118102:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1594+point 2 split 4096 1595)/2 = (430409159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430409159:ℝ)/168755200)/ClassicalSixthBranch.v ((430409159:ℝ)/168755200) = (690738523511:ℝ)/344029882232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1594
  · change lowerPayment 1595 ≤ lowerValue ((point 2 split 4096 1595+point 2 split 4096 1596)/2)
    have hp : lowerPayment 1595 = (194799777751:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1595+point 2 split 4096 1596)/2 = (430467421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430467421:ℝ)/168755200)/ClassicalSixthBranch.v ((430467421:ℝ)/168755200) = (690661209837:ℝ)/343981874344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1595
  · change lowerPayment 1596 ≤ lowerValue ((point 2 split 4096 1596+point 2 split 4096 1597)/2)
    have hp : lowerPayment 1596 = (194896419807:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1596+point 2 split 4096 1597)/2 = (4179861:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4179861:ℝ)/1638400)/ClassicalSixthBranch.v ((4179861:ℝ)/1638400) = (6704698021:ℝ)/3339163752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1596
  · change lowerPayment 1597 ≤ lowerValue ((point 2 split 4096 1597+point 2 split 4096 1598)/2)
    have hp : lowerPayment 1597 = (194993044293:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1597+point 2 split 4096 1598)/2 = (86116789:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86116789:ℝ)/33751040)/ClassicalSixthBranch.v ((86116789:ℝ)/33751040) = (690506582489:ℝ)/343885858568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1597
  · change lowerPayment 1598 ≤ lowerValue ((point 2 split 4096 1598+point 2 split 4096 1599)/2)
    have hp : lowerPayment 1598 = (195089651227:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1598+point 2 split 4096 1599)/2 = (430642207:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430642207:ℝ)/168755200)/ClassicalSixthBranch.v ((430642207:ℝ)/168755200) = (138085853763:ℝ)/68767570136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1598
  · change lowerPayment 1599 ≤ lowerValue ((point 2 split 4096 1599+point 2 split 4096 1600)/2)
    have hp : lowerPayment 1599 = (195186240631:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1599+point 2 split 4096 1600)/2 = (430700469:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430700469:ℝ)/168755200)/ClassicalSixthBranch.v ((430700469:ℝ)/168755200) = (690351955141:ℝ)/343789842792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1599
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_099
