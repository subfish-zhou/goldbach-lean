import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints101
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_101 (j : Fin 16) : lowerPayment (16*101+j.val) ≤
    lowerValue ((point 2 split 4096 (16*101+j.val)+point 2 split 4096 (16*101+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1616 ≤ lowerValue ((point 2 split 4096 1616+point 2 split 4096 1617)/2)
    have hp : lowerPayment 1616 = (196825597722:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1616+point 2 split 4096 1617)/2 = (431690923:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431690923:ℝ)/168755200)/ClassicalSixthBranch.v ((431690923:ℝ)/168755200) = (689037622683:ℝ)/342973708696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1616
  · change lowerPayment 1617 ≤ lowerValue ((point 2 split 4096 1617+point 2 split 4096 1618)/2)
    have hp : lowerPayment 1617 = (196921875002:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1617+point 2 split 4096 1618)/2 = (86349837:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86349837:ℝ)/33751040)/ClassicalSixthBranch.v ((86349837:ℝ)/33751040) = (688960309009:ℝ)/342925700808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1617
  · change lowerPayment 1618 ≤ lowerValue ((point 2 split 4096 1618+point 2 split 4096 1619)/2)
    have hp : lowerPayment 1618 = (197018135131:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1618+point 2 split 4096 1619)/2 = (431807447:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431807447:ℝ)/168755200)/ClassicalSixthBranch.v ((431807447:ℝ)/168755200) = (137776599067:ℝ)/68575538584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1618
  · change lowerPayment 1619 ≤ lowerValue ((point 2 split 4096 1619+point 2 split 4096 1620)/2)
    have hp : lowerPayment 1619 = (197114378131:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1619+point 2 split 4096 1620)/2 = (431865709:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431865709:ℝ)/168755200)/ClassicalSixthBranch.v ((431865709:ℝ)/168755200) = (688805681661:ℝ)/342829685032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1619
  · change lowerPayment 1620 ≤ lowerValue ((point 2 split 4096 1620+point 2 split 4096 1621)/2)
    have hp : lowerPayment 1620 = (197210604021:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1620+point 2 split 4096 1621)/2 = (431923971:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431923971:ℝ)/168755200)/ClassicalSixthBranch.v ((431923971:ℝ)/168755200) = (688728367987:ℝ)/342781677144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1620
  · change lowerPayment 1621 ≤ lowerValue ((point 2 split 4096 1621+point 2 split 4096 1622)/2)
    have hp : lowerPayment 1621 = (197306812820:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1621+point 2 split 4096 1622)/2 = (431982233:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431982233:ℝ)/168755200)/ClassicalSixthBranch.v ((431982233:ℝ)/168755200) = (688651054313:ℝ)/342733669256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1621
  · change lowerPayment 1622 ≤ lowerValue ((point 2 split 4096 1622+point 2 split 4096 1623)/2)
    have hp : lowerPayment 1622 = (197403004549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1622+point 2 split 4096 1623)/2 = (86408099:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86408099:ℝ)/33751040)/ClassicalSixthBranch.v ((86408099:ℝ)/33751040) = (688573740639:ℝ)/342685661368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1622
  · change lowerPayment 1623 ≤ lowerValue ((point 2 split 4096 1623+point 2 split 4096 1624)/2)
    have hp : lowerPayment 1623 = (197499179227:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1623+point 2 split 4096 1624)/2 = (432098757:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432098757:ℝ)/168755200)/ClassicalSixthBranch.v ((432098757:ℝ)/168755200) = (137699285393:ℝ)/68527530696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1623
  · change lowerPayment 1624 ≤ lowerValue ((point 2 split 4096 1624+point 2 split 4096 1625)/2)
    have hp : lowerPayment 1624 = (197595336875:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1624+point 2 split 4096 1625)/2 = (432157019:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432157019:ℝ)/168755200)/ClassicalSixthBranch.v ((432157019:ℝ)/168755200) = (688419113291:ℝ)/342589645592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1624
  · change lowerPayment 1625 ≤ lowerValue ((point 2 split 4096 1625+point 2 split 4096 1626)/2)
    have hp : lowerPayment 1625 = (197691477512:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1625+point 2 split 4096 1626)/2 = (432215281:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432215281:ℝ)/168755200)/ClassicalSixthBranch.v ((432215281:ℝ)/168755200) = (688341799617:ℝ)/342541637704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1625
  · change lowerPayment 1626 ≤ lowerValue ((point 2 split 4096 1626+point 2 split 4096 1627)/2)
    have hp : lowerPayment 1626 = (197787601158:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1626+point 2 split 4096 1627)/2 = (432273543:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432273543:ℝ)/168755200)/ClassicalSixthBranch.v ((432273543:ℝ)/168755200) = (688264485943:ℝ)/342493629816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1626
  · change lowerPayment 1627 ≤ lowerValue ((point 2 split 4096 1627+point 2 split 4096 1628)/2)
    have hp : lowerPayment 1627 = (197883707834:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1627+point 2 split 4096 1628)/2 = (86466361:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86466361:ℝ)/33751040)/ClassicalSixthBranch.v ((86466361:ℝ)/33751040) = (688187172269:ℝ)/342445621928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1627
  · change lowerPayment 1628 ≤ lowerValue ((point 2 split 4096 1628+point 2 split 4096 1629)/2)
    have hp : lowerPayment 1628 = (197979797558:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1628+point 2 split 4096 1629)/2 = (432390067:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432390067:ℝ)/168755200)/ClassicalSixthBranch.v ((432390067:ℝ)/168755200) = (137621971719:ℝ)/68479522808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1628
  · change lowerPayment 1629 ≤ lowerValue ((point 2 split 4096 1629+point 2 split 4096 1630)/2)
    have hp : lowerPayment 1629 = (198075870351:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1629+point 2 split 4096 1630)/2 = (432448329:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432448329:ℝ)/168755200)/ClassicalSixthBranch.v ((432448329:ℝ)/168755200) = (688032544921:ℝ)/342349606152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1629
  · change lowerPayment 1630 ≤ lowerValue ((point 2 split 4096 1630+point 2 split 4096 1631)/2)
    have hp : lowerPayment 1630 = (198171926233:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1630+point 2 split 4096 1631)/2 = (432506591:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432506591:ℝ)/168755200)/ClassicalSixthBranch.v ((432506591:ℝ)/168755200) = (687955231247:ℝ)/342301598264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1630
  · change lowerPayment 1631 ≤ lowerValue ((point 2 split 4096 1631+point 2 split 4096 1632)/2)
    have hp : lowerPayment 1631 = (198267965223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1631+point 2 split 4096 1632)/2 = (432564853:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((432564853:ℝ)/168755200)/ClassicalSixthBranch.v ((432564853:ℝ)/168755200) = (687877917573:ℝ)/342253590376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1631
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_101
