import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints097
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_097 (j : Fin 16) : upperValue ((point (16*97+j.val)+point ((16*97+j.val)+1))/2) ≤ payment (16*97+j.val) := by
  fin_cases j
  · change upperValue ((point (1552)+point ((1552)+1))/2) ≤ payment (1552)
    have hp : payment 1552 = (868951880933:ℝ)/1000000000000 := rfl
    have hx : (point 1552+point 1553)/2 = (1472545:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1552
  · change upperValue ((point (1553)+point ((1553)+1))/2) ≤ payment (1553)
    have hp : payment 1553 = (867086904068:ℝ)/1000000000000 := rfl
    have hx : (point 1553+point 1554)/2 = (4419689:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1553
  · change upperValue ((point (1554)+point ((1554)+1))/2) ≤ payment (1554)
    have hp : payment 1554 = (865222642084:ℝ)/1000000000000 := rfl
    have hx : (point 1554+point 1555)/2 = (4421743:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1554
  · change upperValue ((point (1555)+point ((1555)+1))/2) ≤ payment (1555)
    have hp : payment 1555 = (863359093131:ℝ)/1000000000000 := rfl
    have hx : (point 1555+point 1556)/2 = (1474599:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1555
  · change upperValue ((point (1556)+point ((1556)+1))/2) ≤ payment (1556)
    have hp : payment 1556 = (861496255363:ℝ)/1000000000000 := rfl
    have hx : (point 1556+point 1557)/2 = (4425851:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1556
  · change upperValue ((point (1557)+point ((1557)+1))/2) ≤ payment (1557)
    have hp : payment 1557 = (859634126934:ℝ)/1000000000000 := rfl
    have hx : (point 1557+point 1558)/2 = (4427905:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1557
  · change upperValue ((point (1558)+point ((1558)+1))/2) ≤ payment (1558)
    have hp : payment 1558 = (857772706002:ℝ)/1000000000000 := rfl
    have hx : (point 1558+point 1559)/2 = (1476653:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1558
  · change upperValue ((point (1559)+point ((1559)+1))/2) ≤ payment (1559)
    have hp : payment 1559 = (855911990726:ℝ)/1000000000000 := rfl
    have hx : (point 1559+point 1560)/2 = (4432013:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1559
  · change upperValue ((point (1560)+point ((1560)+1))/2) ≤ payment (1560)
    have hp : payment 1560 = (854051979270:ℝ)/1000000000000 := rfl
    have hx : (point 1560+point 1561)/2 = (4434067:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1560
  · change upperValue ((point (1561)+point ((1561)+1))/2) ≤ payment (1561)
    have hp : payment 1561 = (852192669799:ℝ)/1000000000000 := rfl
    have hx : (point 1561+point 1562)/2 = (1478707:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1561
  · change upperValue ((point (1562)+point ((1562)+1))/2) ≤ payment (1562)
    have hp : payment 1562 = (850334060479:ℝ)/1000000000000 := rfl
    have hx : (point 1562+point 1563)/2 = (4438175:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1562
  · change upperValue ((point (1563)+point ((1563)+1))/2) ≤ payment (1563)
    have hp : payment 1563 = (848476149481:ℝ)/1000000000000 := rfl
    have hx : (point 1563+point 1564)/2 = (4440229:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1563
  · change upperValue ((point (1564)+point ((1564)+1))/2) ≤ payment (1564)
    have hp : payment 1564 = (846618934978:ℝ)/1000000000000 := rfl
    have hx : (point 1564+point 1565)/2 = (1480761:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1564
  · change upperValue ((point (1565)+point ((1565)+1))/2) ≤ payment (1565)
    have hp : payment 1565 = (844762415144:ℝ)/1000000000000 := rfl
    have hx : (point 1565+point 1566)/2 = (4444337:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1565
  · change upperValue ((point (1566)+point ((1566)+1))/2) ≤ payment (1566)
    have hp : payment 1566 = (842906588157:ℝ)/1000000000000 := rfl
    have hx : (point 1566+point 1567)/2 = (4446391:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1566
  · change upperValue ((point (1567)+point ((1567)+1))/2) ≤ payment (1567)
    have hp : payment 1567 = (841051452198:ℝ)/1000000000000 := rfl
    have hx : (point 1567+point 1568)/2 = (1482815:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1567
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_097
