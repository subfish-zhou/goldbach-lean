import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints102
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_102 (j : Fin 16) : upperValue ((point (16*102+j.val)+point ((16*102+j.val)+1))/2) ≤ payment (16*102+j.val) := by
  fin_cases j
  · change upperValue ((point (1632)+point ((1632)+1))/2) ≤ payment (1632)
    have hp : payment 1632 = (721864599564:ℝ)/1000000000000 := rfl
    have hx : (point 1632+point 1633)/2 = (4581955:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1632
  · change upperValue ((point (1633)+point ((1633)+1))/2) ≤ payment (1633)
    have hp : payment 1633 = (720051164420:ℝ)/1000000000000 := rfl
    have hx : (point 1633+point 1634)/2 = (1528003:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1633
  · change upperValue ((point (1634)+point ((1634)+1))/2) ≤ payment (1634)
    have hp : payment 1634 = (718238303602:ℝ)/1000000000000 := rfl
    have hx : (point 1634+point 1635)/2 = (4586063:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1634
  · change upperValue ((point (1635)+point ((1635)+1))/2) ≤ payment (1635)
    have hp : payment 1635 = (716426015444:ℝ)/1000000000000 := rfl
    have hx : (point 1635+point 1636)/2 = (4588117:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1635
  · change upperValue ((point (1636)+point ((1636)+1))/2) ≤ payment (1636)
    have hp : payment 1636 = (714614298278:ℝ)/1000000000000 := rfl
    have hx : (point 1636+point 1637)/2 = (1530057:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1636
  · change upperValue ((point (1637)+point ((1637)+1))/2) ≤ payment (1637)
    have hp : payment 1637 = (712803150441:ℝ)/1000000000000 := rfl
    have hx : (point 1637+point 1638)/2 = (4592225:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1637
  · change upperValue ((point (1638)+point ((1638)+1))/2) ≤ payment (1638)
    have hp : payment 1638 = (710992570269:ℝ)/1000000000000 := rfl
    have hx : (point 1638+point 1639)/2 = (4594279:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1638
  · change upperValue ((point (1639)+point ((1639)+1))/2) ≤ payment (1639)
    have hp : payment 1639 = (709182556102:ℝ)/1000000000000 := rfl
    have hx : (point 1639+point 1640)/2 = (1532111:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1639
  · change upperValue ((point (1640)+point ((1640)+1))/2) ≤ payment (1640)
    have hp : payment 1640 = (707373106283:ℝ)/1000000000000 := rfl
    have hx : (point 1640+point 1641)/2 = (4598387:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1640
  · change upperValue ((point (1641)+point ((1641)+1))/2) ≤ payment (1641)
    have hp : payment 1641 = (705564219154:ℝ)/1000000000000 := rfl
    have hx : (point 1641+point 1642)/2 = (4600441:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1641
  · change upperValue ((point (1642)+point ((1642)+1))/2) ≤ payment (1642)
    have hp : payment 1642 = (703755893061:ℝ)/1000000000000 := rfl
    have hx : (point 1642+point 1643)/2 = (1534165:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1642
  · change upperValue ((point (1643)+point ((1643)+1))/2) ≤ payment (1643)
    have hp : payment 1643 = (701948126353:ℝ)/1000000000000 := rfl
    have hx : (point 1643+point 1644)/2 = (4604549:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1643
  · change upperValue ((point (1644)+point ((1644)+1))/2) ≤ payment (1644)
    have hp : payment 1644 = (700140917378:ℝ)/1000000000000 := rfl
    have hx : (point 1644+point 1645)/2 = (4606603:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1644
  · change upperValue ((point (1645)+point ((1645)+1))/2) ≤ payment (1645)
    have hp : payment 1645 = (698334264487:ℝ)/1000000000000 := rfl
    have hx : (point 1645+point 1646)/2 = (1536219:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1645
  · change upperValue ((point (1646)+point ((1646)+1))/2) ≤ payment (1646)
    have hp : payment 1646 = (696528166036:ℝ)/1000000000000 := rfl
    have hx : (point 1646+point 1647)/2 = (4610711:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1646
  · change upperValue ((point (1647)+point ((1647)+1))/2) ≤ payment (1647)
    have hp : payment 1647 = (694722620378:ℝ)/1000000000000 := rfl
    have hx : (point 1647+point 1648)/2 = (4612765:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1647
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_102
