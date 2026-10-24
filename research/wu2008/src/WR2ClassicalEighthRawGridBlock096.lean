import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints096
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_096 (j : Fin 16) : upperValue ((point (16*96+j.val)+point ((16*96+j.val)+1))/2) ≤ payment (16*96+j.val) := by
  fin_cases j
  · change upperValue ((point (1536)+point ((1536)+1))/2) ≤ payment (1536)
    have hp : payment 1536 = (898890254227:ℝ)/1000000000000 := rfl
    have hx : (point 1536+point 1537)/2 = (4384771:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1536
  · change upperValue ((point (1537)+point ((1537)+1))/2) ≤ payment (1537)
    have hp : payment 1537 = (897013585559:ℝ)/1000000000000 := rfl
    have hx : (point 1537+point 1538)/2 = (1462275:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1537
  · change upperValue ((point (1538)+point ((1538)+1))/2) ≤ payment (1538)
    have hp : payment 1538 = (895137661723:ℝ)/1000000000000 := rfl
    have hx : (point 1538+point 1539)/2 = (4388879:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1538
  · change upperValue ((point (1539)+point ((1539)+1))/2) ≤ payment (1539)
    have hp : payment 1539 = (893262480827:ℝ)/1000000000000 := rfl
    have hx : (point 1539+point 1540)/2 = (4390933:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1539
  · change upperValue ((point (1540)+point ((1540)+1))/2) ≤ payment (1540)
    have hp : payment 1540 = (891388040984:ℝ)/1000000000000 := rfl
    have hx : (point 1540+point 1541)/2 = (1464329:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1540
  · change upperValue ((point (1541)+point ((1541)+1))/2) ≤ payment (1541)
    have hp : payment 1541 = (889514340305:ℝ)/1000000000000 := rfl
    have hx : (point 1541+point 1542)/2 = (4395041:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1541
  · change upperValue ((point (1542)+point ((1542)+1))/2) ≤ payment (1542)
    have hp : payment 1542 = (887641376909:ℝ)/1000000000000 := rfl
    have hx : (point 1542+point 1543)/2 = (4397095:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1542
  · change upperValue ((point (1543)+point ((1543)+1))/2) ≤ payment (1543)
    have hp : payment 1543 = (885769148914:ℝ)/1000000000000 := rfl
    have hx : (point 1543+point 1544)/2 = (1466383:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1543
  · change upperValue ((point (1544)+point ((1544)+1))/2) ≤ payment (1544)
    have hp : payment 1544 = (883897654441:ℝ)/1000000000000 := rfl
    have hx : (point 1544+point 1545)/2 = (4401203:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1544
  · change upperValue ((point (1545)+point ((1545)+1))/2) ≤ payment (1545)
    have hp : payment 1545 = (882026891615:ℝ)/1000000000000 := rfl
    have hx : (point 1545+point 1546)/2 = (4403257:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1545
  · change upperValue ((point (1546)+point ((1546)+1))/2) ≤ payment (1546)
    have hp : payment 1546 = (880156858563:ℝ)/1000000000000 := rfl
    have hx : (point 1546+point 1547)/2 = (1468437:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1546
  · change upperValue ((point (1547)+point ((1547)+1))/2) ≤ payment (1547)
    have hp : payment 1547 = (878287553415:ℝ)/1000000000000 := rfl
    have hx : (point 1547+point 1548)/2 = (4407365:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1547
  · change upperValue ((point (1548)+point ((1548)+1))/2) ≤ payment (1548)
    have hp : payment 1548 = (876418974301:ℝ)/1000000000000 := rfl
    have hx : (point 1548+point 1549)/2 = (4409419:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1548
  · change upperValue ((point (1549)+point ((1549)+1))/2) ≤ payment (1549)
    have hp : payment 1549 = (874551119358:ℝ)/1000000000000 := rfl
    have hx : (point 1549+point 1550)/2 = (1470491:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1549
  · change upperValue ((point (1550)+point ((1550)+1))/2) ≤ payment (1550)
    have hp : payment 1550 = (872683986722:ℝ)/1000000000000 := rfl
    have hx : (point 1550+point 1551)/2 = (4413527:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1550
  · change upperValue ((point (1551)+point ((1551)+1))/2) ≤ payment (1551)
    have hp : payment 1551 = (870817574533:ℝ)/1000000000000 := rfl
    have hx : (point 1551+point 1552)/2 = (4415581:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1551
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_096
