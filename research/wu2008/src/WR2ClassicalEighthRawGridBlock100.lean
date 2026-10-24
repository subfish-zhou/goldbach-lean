import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints100
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_100 (j : Fin 16) : upperValue ((point (16*100+j.val)+point ((16*100+j.val)+1))/2) ≤ payment (16*100+j.val) := by
  fin_cases j
  · change upperValue ((point (1600)+point ((1600)+1))/2) ≤ payment (1600)
    have hp : payment 1600 = (780207860661:ℝ)/1000000000000 := rfl
    have hx : (point 1600+point 1601)/2 = (1505409:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1600
  · change upperValue ((point (1601)+point ((1601)+1))/2) ≤ payment (1601)
    have hp : payment 1601 = (778375153735:ℝ)/1000000000000 := rfl
    have hx : (point 1601+point 1602)/2 = (4518281:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1601
  · change upperValue ((point (1602)+point ((1602)+1))/2) ≤ payment (1602)
    have hp : payment 1602 = (776543075627:ℝ)/1000000000000 := rfl
    have hx : (point 1602+point 1603)/2 = (4520335:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1602
  · change upperValue ((point (1603)+point ((1603)+1))/2) ≤ payment (1603)
    have hp : payment 1603 = (774711624600:ℝ)/1000000000000 := rfl
    have hx : (point 1603+point 1604)/2 = (1507463:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1603
  · change upperValue ((point (1604)+point ((1604)+1))/2) ≤ payment (1604)
    have hp : payment 1604 = (772880798922:ℝ)/1000000000000 := rfl
    have hx : (point 1604+point 1605)/2 = (4524443:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1604
  · change upperValue ((point (1605)+point ((1605)+1))/2) ≤ payment (1605)
    have hp : payment 1605 = (771050596858:ℝ)/1000000000000 := rfl
    have hx : (point 1605+point 1606)/2 = (4526497:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1605
  · change upperValue ((point (1606)+point ((1606)+1))/2) ≤ payment (1606)
    have hp : payment 1606 = (769221016682:ℝ)/1000000000000 := rfl
    have hx : (point 1606+point 1607)/2 = (1509517:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1606
  · change upperValue ((point (1607)+point ((1607)+1))/2) ≤ payment (1607)
    have hp : payment 1607 = (767392056664:ℝ)/1000000000000 := rfl
    have hx : (point 1607+point 1608)/2 = (4530605:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1607
  · change upperValue ((point (1608)+point ((1608)+1))/2) ≤ payment (1608)
    have hp : payment 1608 = (765563715080:ℝ)/1000000000000 := rfl
    have hx : (point 1608+point 1609)/2 = (4532659:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1608
  · change upperValue ((point (1609)+point ((1609)+1))/2) ≤ payment (1609)
    have hp : payment 1609 = (763735990207:ℝ)/1000000000000 := rfl
    have hx : (point 1609+point 1610)/2 = (1511571:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1609
  · change upperValue ((point (1610)+point ((1610)+1))/2) ≤ payment (1610)
    have hp : payment 1610 = (761908880323:ℝ)/1000000000000 := rfl
    have hx : (point 1610+point 1611)/2 = (4536767:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1610
  · change upperValue ((point (1611)+point ((1611)+1))/2) ≤ payment (1611)
    have hp : payment 1611 = (760082383712:ℝ)/1000000000000 := rfl
    have hx : (point 1611+point 1612)/2 = (4538821:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1611
  · change upperValue ((point (1612)+point ((1612)+1))/2) ≤ payment (1612)
    have hp : payment 1612 = (758256498655:ℝ)/1000000000000 := rfl
    have hx : (point 1612+point 1613)/2 = (1513625:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1612
  · change upperValue ((point (1613)+point ((1613)+1))/2) ≤ payment (1613)
    have hp : payment 1613 = (756431223438:ℝ)/1000000000000 := rfl
    have hx : (point 1613+point 1614)/2 = (4542929:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1613
  · change upperValue ((point (1614)+point ((1614)+1))/2) ≤ payment (1614)
    have hp : payment 1614 = (754606556350:ℝ)/1000000000000 := rfl
    have hx : (point 1614+point 1615)/2 = (4544983:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1614
  · change upperValue ((point (1615)+point ((1615)+1))/2) ≤ payment (1615)
    have hp : payment 1615 = (752782495681:ℝ)/1000000000000 := rfl
    have hx : (point 1615+point 1616)/2 = (1515679:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1615
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_100
