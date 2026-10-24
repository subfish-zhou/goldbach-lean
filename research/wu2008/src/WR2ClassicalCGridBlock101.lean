import WR2ClassicalCPayments
import WR2ClassicalCPoints101
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_101 (j : Fin 16) : cPayment (16*101+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*101+j.val)+point (1327/200) 4096 (16*101+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1616 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1616+point (1327/200) 4096 1617)/2)
    have hp : cPayment 1616 = (78040752329:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1616+point (1327/200) 4096 1617)/2 = (4980591:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1616
  · change cPayment 1617 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1617+point (1327/200) 4096 1618)/2)
    have hp : cPayment 1617 = (78021400561:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1617+point (1327/200) 4096 1618)/2 = (996329:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1617
  · change cPayment 1618 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1618+point (1327/200) 4096 1619)/2)
    have hp : cPayment 1618 = (78002019045:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1618+point (1327/200) 4096 1619)/2 = (4982699:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1618
  · change cPayment 1619 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1619+point (1327/200) 4096 1620)/2)
    have hp : cPayment 1619 = (77982607829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1619+point (1327/200) 4096 1620)/2 = (4983753:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1619
  · change cPayment 1620 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1620+point (1327/200) 4096 1621)/2)
    have hp : cPayment 1620 = (77963166960:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1620+point (1327/200) 4096 1621)/2 = (4984807:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1620
  · change cPayment 1621 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1621+point (1327/200) 4096 1622)/2)
    have hp : cPayment 1621 = (77943696484:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1621+point (1327/200) 4096 1622)/2 = (4985861:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1621
  · change cPayment 1622 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1622+point (1327/200) 4096 1623)/2)
    have hp : cPayment 1622 = (77924196449:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1622+point (1327/200) 4096 1623)/2 = (997383:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1622
  · change cPayment 1623 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1623+point (1327/200) 4096 1624)/2)
    have hp : cPayment 1623 = (77904666903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1623+point (1327/200) 4096 1624)/2 = (4987969:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1623
  · change cPayment 1624 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1624+point (1327/200) 4096 1625)/2)
    have hp : cPayment 1624 = (77885107891:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1624+point (1327/200) 4096 1625)/2 = (4989023:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1624
  · change cPayment 1625 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1625+point (1327/200) 4096 1626)/2)
    have hp : cPayment 1625 = (77865519462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1625+point (1327/200) 4096 1626)/2 = (4990077:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1625
  · change cPayment 1626 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1626+point (1327/200) 4096 1627)/2)
    have hp : cPayment 1626 = (77845901661:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1626+point (1327/200) 4096 1627)/2 = (4991131:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1626
  · change cPayment 1627 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1627+point (1327/200) 4096 1628)/2)
    have hp : cPayment 1627 = (77826254535:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1627+point (1327/200) 4096 1628)/2 = (998437:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1627
  · change cPayment 1628 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1628+point (1327/200) 4096 1629)/2)
    have hp : cPayment 1628 = (77806578132:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1628+point (1327/200) 4096 1629)/2 = (4993239:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1628
  · change cPayment 1629 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1629+point (1327/200) 4096 1630)/2)
    have hp : cPayment 1629 = (77786872498:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1629+point (1327/200) 4096 1630)/2 = (4994293:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1629
  · change cPayment 1630 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1630+point (1327/200) 4096 1631)/2)
    have hp : cPayment 1630 = (77767137679:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1630+point (1327/200) 4096 1631)/2 = (4995347:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1630
  · change cPayment 1631 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1631+point (1327/200) 4096 1632)/2)
    have hp : cPayment 1631 = (77747373723:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1631+point (1327/200) 4096 1632)/2 = (4996401:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1631
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_101
