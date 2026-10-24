import WR2ClassicalCPayments
import WR2ClassicalCPoints106
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_106 (j : Fin 16) : cPayment (16*106+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*106+j.val)+point (1327/200) 4096 (16*106+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1696 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1696+point (1327/200) 4096 1697)/2)
    have hp : cPayment 1696 = (76402391110:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1696+point (1327/200) 4096 1697)/2 = (5064911:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1696
  · change cPayment 1697 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1697+point (1327/200) 4096 1698)/2)
    have hp : cPayment 1697 = (76380803667:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1697+point (1327/200) 4096 1698)/2 = (1013193:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1697
  · change cPayment 1698 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1698+point (1327/200) 4096 1699)/2)
    have hp : cPayment 1698 = (76359190057:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1698+point (1327/200) 4096 1699)/2 = (5067019:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1698
  · change cPayment 1699 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1699+point (1327/200) 4096 1700)/2)
    have hp : cPayment 1699 = (76337550322:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1699+point (1327/200) 4096 1700)/2 = (5068073:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1699
  · change cPayment 1700 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1700+point (1327/200) 4096 1701)/2)
    have hp : cPayment 1700 = (76315884506:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1700+point (1327/200) 4096 1701)/2 = (5069127:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1700
  · change cPayment 1701 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1701+point (1327/200) 4096 1702)/2)
    have hp : cPayment 1701 = (76294192649:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1701+point (1327/200) 4096 1702)/2 = (5070181:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1701
  · change cPayment 1702 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1702+point (1327/200) 4096 1703)/2)
    have hp : cPayment 1702 = (76272474795:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1702+point (1327/200) 4096 1703)/2 = (1014247:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1702
  · change cPayment 1703 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1703+point (1327/200) 4096 1704)/2)
    have hp : cPayment 1703 = (76250730985:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1703+point (1327/200) 4096 1704)/2 = (5072289:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1703
  · change cPayment 1704 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1704+point (1327/200) 4096 1705)/2)
    have hp : cPayment 1704 = (76228961261:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1704+point (1327/200) 4096 1705)/2 = (5073343:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1704
  · change cPayment 1705 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1705+point (1327/200) 4096 1706)/2)
    have hp : cPayment 1705 = (76207165665:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1705+point (1327/200) 4096 1706)/2 = (5074397:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1705
  · change cPayment 1706 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1706+point (1327/200) 4096 1707)/2)
    have hp : cPayment 1706 = (76185344239:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1706+point (1327/200) 4096 1707)/2 = (5075451:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1706
  · change cPayment 1707 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1707+point (1327/200) 4096 1708)/2)
    have hp : cPayment 1707 = (76163497024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1707+point (1327/200) 4096 1708)/2 = (1015301:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1707
  · change cPayment 1708 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1708+point (1327/200) 4096 1709)/2)
    have hp : cPayment 1708 = (76141624063:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1708+point (1327/200) 4096 1709)/2 = (5077559:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1708
  · change cPayment 1709 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1709+point (1327/200) 4096 1710)/2)
    have hp : cPayment 1709 = (76119725397:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1709+point (1327/200) 4096 1710)/2 = (5078613:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1709
  · change cPayment 1710 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1710+point (1327/200) 4096 1711)/2)
    have hp : cPayment 1710 = (76097801067:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1710+point (1327/200) 4096 1711)/2 = (5079667:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1710
  · change cPayment 1711 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1711+point (1327/200) 4096 1712)/2)
    have hp : cPayment 1711 = (76075851116:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1711+point (1327/200) 4096 1712)/2 = (5080721:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1711
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_106
