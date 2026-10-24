import WR2ClassicalCPayments
import WR2ClassicalCPoints099
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_099 (j : Fin 16) : cPayment (16*99+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*99+j.val)+point (1327/200) 4096 (16*99+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1584 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1584+point (1327/200) 4096 1585)/2)
    have hp : cPayment 1584 = (78644015401:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1584+point (1327/200) 4096 1585)/2 = (4946863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1584
  · change cPayment 1585 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1585+point (1327/200) 4096 1586)/2)
    have hp : cPayment 1585 = (78625640949:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1585+point (1327/200) 4096 1586)/2 = (4947917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1585
  · change cPayment 1586 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1586+point (1327/200) 4096 1587)/2)
    have hp : cPayment 1586 = (78607235199:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1586+point (1327/200) 4096 1587)/2 = (4948971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1586
  · change cPayment 1587 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1587+point (1327/200) 4096 1588)/2)
    have hp : cPayment 1587 = (78588798202:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1587+point (1327/200) 4096 1588)/2 = (198001:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1587
  · change cPayment 1588 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1588+point (1327/200) 4096 1589)/2)
    have hp : cPayment 1588 = (78570330005:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1588+point (1327/200) 4096 1589)/2 = (4951079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1588
  · change cPayment 1589 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1589+point (1327/200) 4096 1590)/2)
    have hp : cPayment 1589 = (78551830659:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1589+point (1327/200) 4096 1590)/2 = (4952133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1589
  · change cPayment 1590 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1590+point (1327/200) 4096 1591)/2)
    have hp : cPayment 1590 = (78533300213:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1590+point (1327/200) 4096 1591)/2 = (4953187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1590
  · change cPayment 1591 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1591+point (1327/200) 4096 1592)/2)
    have hp : cPayment 1591 = (78514738716:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1591+point (1327/200) 4096 1592)/2 = (4954241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1591
  · change cPayment 1592 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1592+point (1327/200) 4096 1593)/2)
    have hp : cPayment 1592 = (78496146218:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1592+point (1327/200) 4096 1593)/2 = (991059:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1592
  · change cPayment 1593 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1593+point (1327/200) 4096 1594)/2)
    have hp : cPayment 1593 = (78477522767:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1593+point (1327/200) 4096 1594)/2 = (4956349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1593
  · change cPayment 1594 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1594+point (1327/200) 4096 1595)/2)
    have hp : cPayment 1594 = (78458868412:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1594+point (1327/200) 4096 1595)/2 = (4957403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1594
  · change cPayment 1595 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1595+point (1327/200) 4096 1596)/2)
    have hp : cPayment 1595 = (78440183202:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1595+point (1327/200) 4096 1596)/2 = (4958457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1595
  · change cPayment 1596 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1596+point (1327/200) 4096 1597)/2)
    have hp : cPayment 1596 = (78421467187:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1596+point (1327/200) 4096 1597)/2 = (4959511:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1596
  · change cPayment 1597 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1597+point (1327/200) 4096 1598)/2)
    have hp : cPayment 1597 = (78402720415:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1597+point (1327/200) 4096 1598)/2 = (992113:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1597
  · change cPayment 1598 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1598+point (1327/200) 4096 1599)/2)
    have hp : cPayment 1598 = (78383942934:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1598+point (1327/200) 4096 1599)/2 = (4961619:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1598
  · change cPayment 1599 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1599+point (1327/200) 4096 1600)/2)
    have hp : cPayment 1599 = (78365134794:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1599+point (1327/200) 4096 1600)/2 = (4962673:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1599
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_099
