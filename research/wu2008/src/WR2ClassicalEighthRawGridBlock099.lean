import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints099
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_099 (j : Fin 16) : upperValue ((point (16*99+j.val)+point ((16*99+j.val)+1))/2) ≤ payment (16*99+j.val) := by
  fin_cases j
  · change upperValue ((point (1584)+point ((1584)+1))/2) ≤ payment (1584)
    have hp : payment 1584 = (809618116060:ℝ)/1000000000000 := rfl
    have hx : (point 1584+point 1585)/2 = (4483363:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1584
  · change upperValue ((point (1585)+point ((1585)+1))/2) ≤ payment (1585)
    have hp : payment 1585 = (807775110104:ℝ)/1000000000000 := rfl
    have hx : (point 1585+point 1586)/2 = (1495139:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1585
  · change upperValue ((point (1586)+point ((1586)+1))/2) ≤ payment (1586)
    have hp : payment 1586 = (805932761049:ℝ)/1000000000000 := rfl
    have hx : (point 1586+point 1587)/2 = (4487471:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1586
  · change upperValue ((point (1587)+point ((1587)+1))/2) ≤ payment (1587)
    have hp : payment 1587 = (804091067125:ℝ)/1000000000000 := rfl
    have hx : (point 1587+point 1588)/2 = (4489525:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1587
  · change upperValue ((point (1588)+point ((1588)+1))/2) ≤ payment (1588)
    have hp : payment 1588 = (802250026561:ℝ)/1000000000000 := rfl
    have hx : (point 1588+point 1589)/2 = (1497193:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1588
  · change upperValue ((point (1589)+point ((1589)+1))/2) ≤ payment (1589)
    have hp : payment 1589 = (800409637588:ℝ)/1000000000000 := rfl
    have hx : (point 1589+point 1590)/2 = (4493633:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1589
  · change upperValue ((point (1590)+point ((1590)+1))/2) ≤ payment (1590)
    have hp : payment 1590 = (798569898442:ℝ)/1000000000000 := rfl
    have hx : (point 1590+point 1591)/2 = (4495687:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1590
  · change upperValue ((point (1591)+point ((1591)+1))/2) ≤ payment (1591)
    have hp : payment 1591 = (796730807359:ℝ)/1000000000000 := rfl
    have hx : (point 1591+point 1592)/2 = (1499247:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1591
  · change upperValue ((point (1592)+point ((1592)+1))/2) ≤ payment (1592)
    have hp : payment 1592 = (794892362579:ℝ)/1000000000000 := rfl
    have hx : (point 1592+point 1593)/2 = (4499795:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1592
  · change upperValue ((point (1593)+point ((1593)+1))/2) ≤ payment (1593)
    have hp : payment 1593 = (793054562342:ℝ)/1000000000000 := rfl
    have hx : (point 1593+point 1594)/2 = (4501849:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1593
  · change upperValue ((point (1594)+point ((1594)+1))/2) ≤ payment (1594)
    have hp : payment 1594 = (791217404892:ℝ)/1000000000000 := rfl
    have hx : (point 1594+point 1595)/2 = (1501301:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1594
  · change upperValue ((point (1595)+point ((1595)+1))/2) ≤ payment (1595)
    have hp : payment 1595 = (789380888476:ℝ)/1000000000000 := rfl
    have hx : (point 1595+point 1596)/2 = (4505957:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1595
  · change upperValue ((point (1596)+point ((1596)+1))/2) ≤ payment (1596)
    have hp : payment 1596 = (787545011342:ℝ)/1000000000000 := rfl
    have hx : (point 1596+point 1597)/2 = (4508011:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1596
  · change upperValue ((point (1597)+point ((1597)+1))/2) ≤ payment (1597)
    have hp : payment 1597 = (785709771739:ℝ)/1000000000000 := rfl
    have hx : (point 1597+point 1598)/2 = (1503355:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1597
  · change upperValue ((point (1598)+point ((1598)+1))/2) ≤ payment (1598)
    have hp : payment 1598 = (783875167921:ℝ)/1000000000000 := rfl
    have hx : (point 1598+point 1599)/2 = (4512119:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1598
  · change upperValue ((point (1599)+point ((1599)+1))/2) ≤ payment (1599)
    have hp : payment 1599 = (782041198143:ℝ)/1000000000000 := rfl
    have hx : (point 1599+point 1600)/2 = (4514173:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1599
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_099
