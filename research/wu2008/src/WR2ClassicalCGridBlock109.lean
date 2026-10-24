import WR2ClassicalCPayments
import WR2ClassicalCPoints109
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_109 (j : Fin 16) : cPayment (16*109+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*109+j.val)+point (1327/200) 4096 (16*109+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1744 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1744+point (1327/200) 4096 1745)/2)
    have hp : cPayment 1744 = (75337397522:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1744+point (1327/200) 4096 1745)/2 = (5115503:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1744
  · change cPayment 1745 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1745+point (1327/200) 4096 1746)/2)
    have hp : cPayment 1745 = (75314600747:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1745+point (1327/200) 4096 1746)/2 = (5116557:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1745
  · change cPayment 1746 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1746+point (1327/200) 4096 1747)/2)
    have hp : cPayment 1746 = (75291779770:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1746+point (1327/200) 4096 1747)/2 = (5117611:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1746
  · change cPayment 1747 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1747+point (1327/200) 4096 1748)/2)
    have hp : cPayment 1747 = (75268934629:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1747+point (1327/200) 4096 1748)/2 = (1023733:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1747
  · change cPayment 1748 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1748+point (1327/200) 4096 1749)/2)
    have hp : cPayment 1748 = (75246065363:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1748+point (1327/200) 4096 1749)/2 = (5119719:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1748
  · change cPayment 1749 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1749+point (1327/200) 4096 1750)/2)
    have hp : cPayment 1749 = (75223172013:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1749+point (1327/200) 4096 1750)/2 = (5120773:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1749
  · change cPayment 1750 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1750+point (1327/200) 4096 1751)/2)
    have hp : cPayment 1750 = (75200254617:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1750+point (1327/200) 4096 1751)/2 = (5121827:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1750
  · change cPayment 1751 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1751+point (1327/200) 4096 1752)/2)
    have hp : cPayment 1751 = (75177313215:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1751+point (1327/200) 4096 1752)/2 = (5122881:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1751
  · change cPayment 1752 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1752+point (1327/200) 4096 1753)/2)
    have hp : cPayment 1752 = (75154347846:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1752+point (1327/200) 4096 1753)/2 = (1024787:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1752
  · change cPayment 1753 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1753+point (1327/200) 4096 1754)/2)
    have hp : cPayment 1753 = (75131358549:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1753+point (1327/200) 4096 1754)/2 = (5124989:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1753
  · change cPayment 1754 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1754+point (1327/200) 4096 1755)/2)
    have hp : cPayment 1754 = (75108345363:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1754+point (1327/200) 4096 1755)/2 = (5126043:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1754
  · change cPayment 1755 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1755+point (1327/200) 4096 1756)/2)
    have hp : cPayment 1755 = (75085308328:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1755+point (1327/200) 4096 1756)/2 = (5127097:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1755
  · change cPayment 1756 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1756+point (1327/200) 4096 1757)/2)
    have hp : cPayment 1756 = (75062247483:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1756+point (1327/200) 4096 1757)/2 = (5128151:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1756
  · change cPayment 1757 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1757+point (1327/200) 4096 1758)/2)
    have hp : cPayment 1757 = (75039162865:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1757+point (1327/200) 4096 1758)/2 = (1025841:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1757
  · change cPayment 1758 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1758+point (1327/200) 4096 1759)/2)
    have hp : cPayment 1758 = (75016054516:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1758+point (1327/200) 4096 1759)/2 = (5130259:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1758
  · change cPayment 1759 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1759+point (1327/200) 4096 1760)/2)
    have hp : cPayment 1759 = (74992922472:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1759+point (1327/200) 4096 1760)/2 = (5131313:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1759
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_109
