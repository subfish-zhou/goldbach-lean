import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints106
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_106 (j : Fin 16) : upperValue ((point (16*106+j.val)+point ((16*106+j.val)+1))/2) ≤ payment (16*106+j.val) := by
  fin_cases j
  · change upperValue ((point (1696)+point ((1696)+1))/2) ≤ payment (1696)
    have hp : payment 1696 = (606894321382:ℝ)/1000000000000 := rfl
    have hx : (point 1696+point 1697)/2 = (1571137:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1696
  · change upperValue ((point (1697)+point ((1697)+1))/2) ≤ payment (1697)
    have hp : payment 1697 = (605114360216:ℝ)/1000000000000 := rfl
    have hx : (point 1697+point 1698)/2 = (4715465:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1697
  · change upperValue ((point (1698)+point ((1698)+1))/2) ≤ payment (1698)
    have hp : payment 1698 = (603334870437:ℝ)/1000000000000 := rfl
    have hx : (point 1698+point 1699)/2 = (4717519:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1698
  · change upperValue ((point (1699)+point ((1699)+1))/2) ≤ payment (1699)
    have hp : payment 1699 = (601555850494:ℝ)/1000000000000 := rfl
    have hx : (point 1699+point 1700)/2 = (1573191:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1699
  · change upperValue ((point (1700)+point ((1700)+1))/2) ≤ payment (1700)
    have hp : payment 1700 = (599777298838:ℝ)/1000000000000 := rfl
    have hx : (point 1700+point 1701)/2 = (4721627:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1700
  · change upperValue ((point (1701)+point ((1701)+1))/2) ≤ payment (1701)
    have hp : payment 1701 = (597999213922:ℝ)/1000000000000 := rfl
    have hx : (point 1701+point 1702)/2 = (4723681:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1701
  · change upperValue ((point (1702)+point ((1702)+1))/2) ≤ payment (1702)
    have hp : payment 1702 = (596221594201:ℝ)/1000000000000 := rfl
    have hx : (point 1702+point 1703)/2 = (1575245:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1702
  · change upperValue ((point (1703)+point ((1703)+1))/2) ≤ payment (1703)
    have hp : payment 1703 = (594444438131:ℝ)/1000000000000 := rfl
    have hx : (point 1703+point 1704)/2 = (4727789:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1703
  · change upperValue ((point (1704)+point ((1704)+1))/2) ≤ payment (1704)
    have hp : payment 1704 = (592667744171:ℝ)/1000000000000 := rfl
    have hx : (point 1704+point 1705)/2 = (4729843:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1704
  · change upperValue ((point (1705)+point ((1705)+1))/2) ≤ payment (1705)
    have hp : payment 1705 = (590891510779:ℝ)/1000000000000 := rfl
    have hx : (point 1705+point 1706)/2 = (1577299:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1705
  · change upperValue ((point (1706)+point ((1706)+1))/2) ≤ payment (1706)
    have hp : payment 1706 = (589115736417:ℝ)/1000000000000 := rfl
    have hx : (point 1706+point 1707)/2 = (4733951:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1706
  · change upperValue ((point (1707)+point ((1707)+1))/2) ≤ payment (1707)
    have hp : payment 1707 = (587340419547:ℝ)/1000000000000 := rfl
    have hx : (point 1707+point 1708)/2 = (4736005:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1707
  · change upperValue ((point (1708)+point ((1708)+1))/2) ≤ payment (1708)
    have hp : payment 1708 = (585565558636:ℝ)/1000000000000 := rfl
    have hx : (point 1708+point 1709)/2 = (1579353:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1708
  · change upperValue ((point (1709)+point ((1709)+1))/2) ≤ payment (1709)
    have hp : payment 1709 = (583791152147:ℝ)/1000000000000 := rfl
    have hx : (point 1709+point 1710)/2 = (4740113:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1709
  · change upperValue ((point (1710)+point ((1710)+1))/2) ≤ payment (1710)
    have hp : payment 1710 = (582017198550:ℝ)/1000000000000 := rfl
    have hx : (point 1710+point 1711)/2 = (4742167:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1710
  · change upperValue ((point (1711)+point ((1711)+1))/2) ≤ payment (1711)
    have hp : payment 1711 = (580243696314:ℝ)/1000000000000 := rfl
    have hx : (point 1711+point 1712)/2 = (1581407:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1711
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_106
