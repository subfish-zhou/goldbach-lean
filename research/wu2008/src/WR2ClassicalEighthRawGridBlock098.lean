import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints098
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_098 (j : Fin 16) : upperValue ((point (16*98+j.val)+point ((16*98+j.val)+1))/2) ≤ payment (16*98+j.val) := by
  fin_cases j
  · change upperValue ((point (1568)+point ((1568)+1))/2) ≤ payment (1568)
    have hp : payment 1568 = (839197005447:ℝ)/1000000000000 := rfl
    have hx : (point 1568+point 1569)/2 = (4450499:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1568
  · change upperValue ((point (1569)+point ((1569)+1))/2) ≤ payment (1569)
    have hp : payment 1569 = (837343246090:ℝ)/1000000000000 := rfl
    have hx : (point 1569+point 1570)/2 = (4452553:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1569
  · change upperValue ((point (1570)+point ((1570)+1))/2) ≤ payment (1570)
    have hp : payment 1570 = (835490172314:ℝ)/1000000000000 := rfl
    have hx : (point 1570+point 1571)/2 = (1484869:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1570
  · change upperValue ((point (1571)+point ((1571)+1))/2) ≤ payment (1571)
    have hp : payment 1571 = (833637782310:ℝ)/1000000000000 := rfl
    have hx : (point 1571+point 1572)/2 = (4456661:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1571
  · change upperValue ((point (1572)+point ((1572)+1))/2) ≤ payment (1572)
    have hp : payment 1572 = (831786074268:ℝ)/1000000000000 := rfl
    have hx : (point 1572+point 1573)/2 = (4458715:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1572
  · change upperValue ((point (1573)+point ((1573)+1))/2) ≤ payment (1573)
    have hp : payment 1573 = (829935046383:ℝ)/1000000000000 := rfl
    have hx : (point 1573+point 1574)/2 = (1486923:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1573
  · change upperValue ((point (1574)+point ((1574)+1))/2) ≤ payment (1574)
    have hp : payment 1574 = (828084696853:ℝ)/1000000000000 := rfl
    have hx : (point 1574+point 1575)/2 = (4462823:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1574
  · change upperValue ((point (1575)+point ((1575)+1))/2) ≤ payment (1575)
    have hp : payment 1575 = (826235023876:ℝ)/1000000000000 := rfl
    have hx : (point 1575+point 1576)/2 = (4464877:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1575
  · change upperValue ((point (1576)+point ((1576)+1))/2) ≤ payment (1576)
    have hp : payment 1576 = (824386025655:ℝ)/1000000000000 := rfl
    have hx : (point 1576+point 1577)/2 = (1488977:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1576
  · change upperValue ((point (1577)+point ((1577)+1))/2) ≤ payment (1577)
    have hp : payment 1577 = (822537700393:ℝ)/1000000000000 := rfl
    have hx : (point 1577+point 1578)/2 = (4468985:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1577
  · change upperValue ((point (1578)+point ((1578)+1))/2) ≤ payment (1578)
    have hp : payment 1578 = (820690046297:ℝ)/1000000000000 := rfl
    have hx : (point 1578+point 1579)/2 = (4471039:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1578
  · change upperValue ((point (1579)+point ((1579)+1))/2) ≤ payment (1579)
    have hp : payment 1579 = (818843061575:ℝ)/1000000000000 := rfl
    have hx : (point 1579+point 1580)/2 = (1491031:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1579
  · change upperValue ((point (1580)+point ((1580)+1))/2) ≤ payment (1580)
    have hp : payment 1580 = (816996744439:ℝ)/1000000000000 := rfl
    have hx : (point 1580+point 1581)/2 = (4475147:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1580
  · change upperValue ((point (1581)+point ((1581)+1))/2) ≤ payment (1581)
    have hp : payment 1581 = (815151093103:ℝ)/1000000000000 := rfl
    have hx : (point 1581+point 1582)/2 = (4477201:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1581
  · change upperValue ((point (1582)+point ((1582)+1))/2) ≤ payment (1582)
    have hp : payment 1582 = (813306105782:ℝ)/1000000000000 := rfl
    have hx : (point 1582+point 1583)/2 = (1493085:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1582
  · change upperValue ((point (1583)+point ((1583)+1))/2) ≤ payment (1583)
    have hp : payment 1583 = (811461780694:ℝ)/1000000000000 := rfl
    have hx : (point 1583+point 1584)/2 = (4481309:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1583
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_098
