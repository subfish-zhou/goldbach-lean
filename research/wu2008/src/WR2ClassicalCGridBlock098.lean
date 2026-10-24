import WR2ClassicalCPayments
import WR2ClassicalCPoints098
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_098 (j : Fin 16) : cPayment (16*98+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*98+j.val)+point (1327/200) 4096 (16*98+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1568 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1568+point (1327/200) 4096 1569)/2)
    have hp : cPayment 1568 = (78933709468:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1568+point (1327/200) 4096 1569)/2 = (4929999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1568
  · change cPayment 1569 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1569+point (1327/200) 4096 1570)/2)
    have hp : cPayment 1569 = (78915842571:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1569+point (1327/200) 4096 1570)/2 = (4931053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1569
  · change cPayment 1570 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1570+point (1327/200) 4096 1571)/2)
    have hp : cPayment 1570 = (78897943574:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1570+point (1327/200) 4096 1571)/2 = (4932107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1570
  · change cPayment 1571 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1571+point (1327/200) 4096 1572)/2)
    have hp : cPayment 1571 = (78880012528:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1571+point (1327/200) 4096 1572)/2 = (4933161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1571
  · change cPayment 1572 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1572+point (1327/200) 4096 1573)/2)
    have hp : cPayment 1572 = (78862049484:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1572+point (1327/200) 4096 1573)/2 = (986843:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1572
  · change cPayment 1573 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1573+point (1327/200) 4096 1574)/2)
    have hp : cPayment 1573 = (78844054492:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1573+point (1327/200) 4096 1574)/2 = (4935269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1573
  · change cPayment 1574 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1574+point (1327/200) 4096 1575)/2)
    have hp : cPayment 1574 = (78826027603:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1574+point (1327/200) 4096 1575)/2 = (4936323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1574
  · change cPayment 1575 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1575+point (1327/200) 4096 1576)/2)
    have hp : cPayment 1575 = (78807968866:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1575+point (1327/200) 4096 1576)/2 = (4937377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1575
  · change cPayment 1576 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1576+point (1327/200) 4096 1577)/2)
    have hp : cPayment 1576 = (78789878333:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1576+point (1327/200) 4096 1577)/2 = (4938431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1576
  · change cPayment 1577 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1577+point (1327/200) 4096 1578)/2)
    have hp : cPayment 1577 = (78771756054:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1577+point (1327/200) 4096 1578)/2 = (987897:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1577
  · change cPayment 1578 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1578+point (1327/200) 4096 1579)/2)
    have hp : cPayment 1578 = (78753602078:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1578+point (1327/200) 4096 1579)/2 = (4940539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1578
  · change cPayment 1579 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1579+point (1327/200) 4096 1580)/2)
    have hp : cPayment 1579 = (78735416457:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1579+point (1327/200) 4096 1580)/2 = (4941593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1579
  · change cPayment 1580 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1580+point (1327/200) 4096 1581)/2)
    have hp : cPayment 1580 = (78717199238:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1580+point (1327/200) 4096 1581)/2 = (4942647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1580
  · change cPayment 1581 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1581+point (1327/200) 4096 1582)/2)
    have hp : cPayment 1581 = (78698950474:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1581+point (1327/200) 4096 1582)/2 = (4943701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1581
  · change cPayment 1582 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1582+point (1327/200) 4096 1583)/2)
    have hp : cPayment 1582 = (78680670213:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1582+point (1327/200) 4096 1583)/2 = (988951:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1582
  · change cPayment 1583 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1583+point (1327/200) 4096 1584)/2)
    have hp : cPayment 1583 = (78662358505:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1583+point (1327/200) 4096 1584)/2 = (4945809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1583
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_098
