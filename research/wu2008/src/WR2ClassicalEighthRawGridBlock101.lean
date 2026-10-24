import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints101
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_101 (j : Fin 16) : upperValue ((point (16*101+j.val)+point ((16*101+j.val)+1))/2) ≤ payment (16*101+j.val) := by
  fin_cases j
  · change upperValue ((point (1616)+point ((1616)+1))/2) ≤ payment (1616)
    have hp : payment 1616 = (750959039722:ℝ)/1000000000000 := rfl
    have hx : (point 1616+point 1617)/2 = (4549091:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1616
  · change upperValue ((point (1617)+point ((1617)+1))/2) ≤ payment (1617)
    have hp : payment 1617 = (749136186768:ℝ)/1000000000000 := rfl
    have hx : (point 1617+point 1618)/2 = (4551145:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1617
  · change upperValue ((point (1618)+point ((1618)+1))/2) ≤ payment (1618)
    have hp : payment 1618 = (747313935114:ℝ)/1000000000000 := rfl
    have hx : (point 1618+point 1619)/2 = (1517733:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1618
  · change upperValue ((point (1619)+point ((1619)+1))/2) ≤ payment (1619)
    have hp : payment 1619 = (745492283061:ℝ)/1000000000000 := rfl
    have hx : (point 1619+point 1620)/2 = (4555253:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1619
  · change upperValue ((point (1620)+point ((1620)+1))/2) ≤ payment (1620)
    have hp : payment 1620 = (743671228908:ℝ)/1000000000000 := rfl
    have hx : (point 1620+point 1621)/2 = (4557307:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1620
  · change upperValue ((point (1621)+point ((1621)+1))/2) ≤ payment (1621)
    have hp : payment 1621 = (741850770957:ℝ)/1000000000000 := rfl
    have hx : (point 1621+point 1622)/2 = (1519787:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1621
  · change upperValue ((point (1622)+point ((1622)+1))/2) ≤ payment (1622)
    have hp : payment 1622 = (740030907515:ℝ)/1000000000000 := rfl
    have hx : (point 1622+point 1623)/2 = (4561415:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1622
  · change upperValue ((point (1623)+point ((1623)+1))/2) ≤ payment (1623)
    have hp : payment 1623 = (738211636886:ℝ)/1000000000000 := rfl
    have hx : (point 1623+point 1624)/2 = (4563469:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1623
  · change upperValue ((point (1624)+point ((1624)+1))/2) ≤ payment (1624)
    have hp : payment 1624 = (736392957382:ℝ)/1000000000000 := rfl
    have hx : (point 1624+point 1625)/2 = (1521841:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1624
  · change upperValue ((point (1625)+point ((1625)+1))/2) ≤ payment (1625)
    have hp : payment 1625 = (734574867313:ℝ)/1000000000000 := rfl
    have hx : (point 1625+point 1626)/2 = (4567577:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1625
  · change upperValue ((point (1626)+point ((1626)+1))/2) ≤ payment (1626)
    have hp : payment 1626 = (732757364991:ℝ)/1000000000000 := rfl
    have hx : (point 1626+point 1627)/2 = (4569631:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1626
  · change upperValue ((point (1627)+point ((1627)+1))/2) ≤ payment (1627)
    have hp : payment 1627 = (730940448732:ℝ)/1000000000000 := rfl
    have hx : (point 1627+point 1628)/2 = (1523895:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1627
  · change upperValue ((point (1628)+point ((1628)+1))/2) ≤ payment (1628)
    have hp : payment 1628 = (729124116854:ℝ)/1000000000000 := rfl
    have hx : (point 1628+point 1629)/2 = (4573739:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1628
  · change upperValue ((point (1629)+point ((1629)+1))/2) ≤ payment (1629)
    have hp : payment 1629 = (727308367676:ℝ)/1000000000000 := rfl
    have hx : (point 1629+point 1630)/2 = (4575793:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1629
  · change upperValue ((point (1630)+point ((1630)+1))/2) ≤ payment (1630)
    have hp : payment 1630 = (725493199519:ℝ)/1000000000000 := rfl
    have hx : (point 1630+point 1631)/2 = (1525949:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1630
  · change upperValue ((point (1631)+point ((1631)+1))/2) ≤ payment (1631)
    have hp : payment 1631 = (723678610706:ℝ)/1000000000000 := rfl
    have hx : (point 1631+point 1632)/2 = (4579901:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1631
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_101
