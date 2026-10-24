import WR2ClassicalCPayments
import WR2ClassicalCPoints097
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_097 (j : Fin 16) : cPayment (16*97+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*97+j.val)+point (1327/200) 4096 (16*97+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1552 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1552+point (1327/200) 4096 1553)/2)
    have hp : cPayment 1552 = (79215172684:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1552+point (1327/200) 4096 1553)/2 = (982627:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1552
  · change cPayment 1553 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1553+point (1327/200) 4096 1554)/2)
    have hp : cPayment 1553 = (79197826326:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1553+point (1327/200) 4096 1554)/2 = (4914189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1553
  · change cPayment 1554 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1554+point (1327/200) 4096 1555)/2)
    have hp : cPayment 1554 = (79180447049:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1554+point (1327/200) 4096 1555)/2 = (4915243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1554
  · change cPayment 1555 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1555+point (1327/200) 4096 1556)/2)
    have hp : cPayment 1555 = (79163034903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1555+point (1327/200) 4096 1556)/2 = (4916297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1555
  · change cPayment 1556 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1556+point (1327/200) 4096 1557)/2)
    have hp : cPayment 1556 = (79145589941:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1556+point (1327/200) 4096 1557)/2 = (4917351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1556
  · change cPayment 1557 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1557+point (1327/200) 4096 1558)/2)
    have hp : cPayment 1557 = (79128112215:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1557+point (1327/200) 4096 1558)/2 = (983681:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1557
  · change cPayment 1558 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1558+point (1327/200) 4096 1559)/2)
    have hp : cPayment 1558 = (79110601776:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1558+point (1327/200) 4096 1559)/2 = (4919459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1558
  · change cPayment 1559 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1559+point (1327/200) 4096 1560)/2)
    have hp : cPayment 1559 = (79093058675:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1559+point (1327/200) 4096 1560)/2 = (4920513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1559
  · change cPayment 1560 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1560+point (1327/200) 4096 1561)/2)
    have hp : cPayment 1560 = (79075482964:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1560+point (1327/200) 4096 1561)/2 = (4921567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1560
  · change cPayment 1561 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1561+point (1327/200) 4096 1562)/2)
    have hp : cPayment 1561 = (79057874695:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1561+point (1327/200) 4096 1562)/2 = (4922621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1561
  · change cPayment 1562 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1562+point (1327/200) 4096 1563)/2)
    have hp : cPayment 1562 = (79040233918:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1562+point (1327/200) 4096 1563)/2 = (196947:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1562
  · change cPayment 1563 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1563+point (1327/200) 4096 1564)/2)
    have hp : cPayment 1563 = (79022560685:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1563+point (1327/200) 4096 1564)/2 = (4924729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1563
  · change cPayment 1564 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1564+point (1327/200) 4096 1565)/2)
    have hp : cPayment 1564 = (79004855048:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1564+point (1327/200) 4096 1565)/2 = (4925783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1564
  · change cPayment 1565 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1565+point (1327/200) 4096 1566)/2)
    have hp : cPayment 1565 = (78987117056:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1565+point (1327/200) 4096 1566)/2 = (4926837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1565
  · change cPayment 1566 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1566+point (1327/200) 4096 1567)/2)
    have hp : cPayment 1566 = (78969346762:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1566+point (1327/200) 4096 1567)/2 = (4927891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1566
  · change cPayment 1567 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1567+point (1327/200) 4096 1568)/2)
    have hp : cPayment 1567 = (78951544215:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1567+point (1327/200) 4096 1568)/2 = (985789:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1567
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_097
