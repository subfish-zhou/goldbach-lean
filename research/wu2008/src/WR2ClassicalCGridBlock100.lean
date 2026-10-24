import WR2ClassicalCPayments
import WR2ClassicalCPoints100
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_100 (j : Fin 16) : cPayment (16*100+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*100+j.val)+point (1327/200) 4096 (16*100+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1600 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1600+point (1327/200) 4096 1601)/2)
    have hp : cPayment 1600 = (78346296043:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1600+point (1327/200) 4096 1601)/2 = (4963727:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1600
  · change cPayment 1601 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1601+point (1327/200) 4096 1602)/2)
    have hp : cPayment 1601 = (78327426730:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1601+point (1327/200) 4096 1602)/2 = (4964781:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1601
  · change cPayment 1602 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1602+point (1327/200) 4096 1603)/2)
    have hp : cPayment 1602 = (78308526903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1602+point (1327/200) 4096 1603)/2 = (993167:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1602
  · change cPayment 1603 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1603+point (1327/200) 4096 1604)/2)
    have hp : cPayment 1603 = (78289596610:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1603+point (1327/200) 4096 1604)/2 = (4966889:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1603
  · change cPayment 1604 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1604+point (1327/200) 4096 1605)/2)
    have hp : cPayment 1604 = (78270635899:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1604+point (1327/200) 4096 1605)/2 = (4967943:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1604
  · change cPayment 1605 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1605+point (1327/200) 4096 1606)/2)
    have hp : cPayment 1605 = (78251644820:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1605+point (1327/200) 4096 1606)/2 = (4968997:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1605
  · change cPayment 1606 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1606+point (1327/200) 4096 1607)/2)
    have hp : cPayment 1606 = (78232623420:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1606+point (1327/200) 4096 1607)/2 = (4970051:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1606
  · change cPayment 1607 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1607+point (1327/200) 4096 1608)/2)
    have hp : cPayment 1607 = (78213571747:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1607+point (1327/200) 4096 1608)/2 = (994221:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1607
  · change cPayment 1608 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1608+point (1327/200) 4096 1609)/2)
    have hp : cPayment 1608 = (78194489850:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1608+point (1327/200) 4096 1609)/2 = (4972159:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1608
  · change cPayment 1609 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1609+point (1327/200) 4096 1610)/2)
    have hp : cPayment 1609 = (78175377776:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1609+point (1327/200) 4096 1610)/2 = (4973213:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1609
  · change cPayment 1610 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1610+point (1327/200) 4096 1611)/2)
    have hp : cPayment 1610 = (78156235573:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1610+point (1327/200) 4096 1611)/2 = (4974267:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1610
  · change cPayment 1611 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1611+point (1327/200) 4096 1612)/2)
    have hp : cPayment 1611 = (78137063290:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1611+point (1327/200) 4096 1612)/2 = (4975321:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1611
  · change cPayment 1612 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1612+point (1327/200) 4096 1613)/2)
    have hp : cPayment 1612 = (78117860973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1612+point (1327/200) 4096 1613)/2 = (199055:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1612
  · change cPayment 1613 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1613+point (1327/200) 4096 1614)/2)
    have hp : cPayment 1613 = (78098628671:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1613+point (1327/200) 4096 1614)/2 = (4977429:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1613
  · change cPayment 1614 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1614+point (1327/200) 4096 1615)/2)
    have hp : cPayment 1614 = (78079366431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1614+point (1327/200) 4096 1615)/2 = (4978483:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1614
  · change cPayment 1615 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1615+point (1327/200) 4096 1616)/2)
    have hp : cPayment 1615 = (78060074301:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1615+point (1327/200) 4096 1616)/2 = (4979537:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1615
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_100
