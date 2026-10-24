import WR2ClassicalCPayments
import WR2ClassicalCPoints104
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_104 (j : Fin 16) : cPayment (16*104+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*104+j.val)+point (1327/200) 4096 (16*104+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1664 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1664+point (1327/200) 4096 1665)/2)
    have hp : cPayment 1664 = (77079117305:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1664+point (1327/200) 4096 1665)/2 = (5031183:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1664
  · change cPayment 1665 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1665+point (1327/200) 4096 1666)/2)
    have hp : cPayment 1665 = (77058389866:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1665+point (1327/200) 4096 1666)/2 = (5032237:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1665
  · change cPayment 1666 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1666+point (1327/200) 4096 1667)/2)
    have hp : cPayment 1666 = (77037634877:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1666+point (1327/200) 4096 1667)/2 = (5033291:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1666
  · change cPayment 1667 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1667+point (1327/200) 4096 1668)/2)
    have hp : cPayment 1667 = (77016852381:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1667+point (1327/200) 4096 1668)/2 = (1006869:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1667
  · change cPayment 1668 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1668+point (1327/200) 4096 1669)/2)
    have hp : cPayment 1668 = (76996042422:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1668+point (1327/200) 4096 1669)/2 = (5035399:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1668
  · change cPayment 1669 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1669+point (1327/200) 4096 1670)/2)
    have hp : cPayment 1669 = (76975205045:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1669+point (1327/200) 4096 1670)/2 = (5036453:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1669
  · change cPayment 1670 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1670+point (1327/200) 4096 1671)/2)
    have hp : cPayment 1670 = (76954340294:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1670+point (1327/200) 4096 1671)/2 = (5037507:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1670
  · change cPayment 1671 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1671+point (1327/200) 4096 1672)/2)
    have hp : cPayment 1671 = (76933448212:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1671+point (1327/200) 4096 1672)/2 = (5038561:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1671
  · change cPayment 1672 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1672+point (1327/200) 4096 1673)/2)
    have hp : cPayment 1672 = (76912528844:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1672+point (1327/200) 4096 1673)/2 = (1007923:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1672
  · change cPayment 1673 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1673+point (1327/200) 4096 1674)/2)
    have hp : cPayment 1673 = (76891582233:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1673+point (1327/200) 4096 1674)/2 = (5040669:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1673
  · change cPayment 1674 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1674+point (1327/200) 4096 1675)/2)
    have hp : cPayment 1674 = (76870608424:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1674+point (1327/200) 4096 1675)/2 = (5041723:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1674
  · change cPayment 1675 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1675+point (1327/200) 4096 1676)/2)
    have hp : cPayment 1675 = (76849607459:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1675+point (1327/200) 4096 1676)/2 = (5042777:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1675
  · change cPayment 1676 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1676+point (1327/200) 4096 1677)/2)
    have hp : cPayment 1676 = (76828579382:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1676+point (1327/200) 4096 1677)/2 = (5043831:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1676
  · change cPayment 1677 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1677+point (1327/200) 4096 1678)/2)
    have hp : cPayment 1677 = (76807524238:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1677+point (1327/200) 4096 1678)/2 = (1008977:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1677
  · change cPayment 1678 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1678+point (1327/200) 4096 1679)/2)
    have hp : cPayment 1678 = (76786442069:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1678+point (1327/200) 4096 1679)/2 = (5045939:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1678
  · change cPayment 1679 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1679+point (1327/200) 4096 1680)/2)
    have hp : cPayment 1679 = (76765332919:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1679+point (1327/200) 4096 1680)/2 = (5046993:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1679
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_104
