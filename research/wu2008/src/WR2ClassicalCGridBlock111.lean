import WR2ClassicalCPayments
import WR2ClassicalCPoints111
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_111 (j : Fin 16) : cPayment (16*111+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*111+j.val)+point (1327/200) 4096 (16*111+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1776 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1776+point (1327/200) 4096 1777)/2)
    have hp : cPayment 1776 = (74596089980:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1776+point (1327/200) 4096 1777)/2 = (5149231:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1776
  · change cPayment 1777 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1777+point (1327/200) 4096 1778)/2)
    have hp : cPayment 1777 = (74572538032:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1777+point (1327/200) 4096 1778)/2 = (1030057:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1777
  · change cPayment 1778 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1778+point (1327/200) 4096 1779)/2)
    have hp : cPayment 1778 = (74548963120:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1778+point (1327/200) 4096 1779)/2 = (5151339:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1778
  · change cPayment 1779 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1779+point (1327/200) 4096 1780)/2)
    have hp : cPayment 1779 = (74525365279:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1779+point (1327/200) 4096 1780)/2 = (5152393:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1779
  · change cPayment 1780 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1780+point (1327/200) 4096 1781)/2)
    have hp : cPayment 1780 = (74501744548:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1780+point (1327/200) 4096 1781)/2 = (5153447:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1780
  · change cPayment 1781 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1781+point (1327/200) 4096 1782)/2)
    have hp : cPayment 1781 = (74478100965:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1781+point (1327/200) 4096 1782)/2 = (5154501:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1781
  · change cPayment 1782 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1782+point (1327/200) 4096 1783)/2)
    have hp : cPayment 1782 = (74454434567:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1782+point (1327/200) 4096 1783)/2 = (1031111:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1782
  · change cPayment 1783 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1783+point (1327/200) 4096 1784)/2)
    have hp : cPayment 1783 = (74430745393:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1783+point (1327/200) 4096 1784)/2 = (5156609:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1783
  · change cPayment 1784 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1784+point (1327/200) 4096 1785)/2)
    have hp : cPayment 1784 = (74407033478:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1784+point (1327/200) 4096 1785)/2 = (5157663:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1784
  · change cPayment 1785 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1785+point (1327/200) 4096 1786)/2)
    have hp : cPayment 1785 = (74383298862:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1785+point (1327/200) 4096 1786)/2 = (5158717:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1785
  · change cPayment 1786 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1786+point (1327/200) 4096 1787)/2)
    have hp : cPayment 1786 = (74359541581:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1786+point (1327/200) 4096 1787)/2 = (5159771:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1786
  · change cPayment 1787 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1787+point (1327/200) 4096 1788)/2)
    have hp : cPayment 1787 = (74335761672:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1787+point (1327/200) 4096 1788)/2 = (206433:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1787
  · change cPayment 1788 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1788+point (1327/200) 4096 1789)/2)
    have hp : cPayment 1788 = (74311959174:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1788+point (1327/200) 4096 1789)/2 = (5161879:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1788
  · change cPayment 1789 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1789+point (1327/200) 4096 1790)/2)
    have hp : cPayment 1789 = (74288134123:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1789+point (1327/200) 4096 1790)/2 = (5162933:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1789
  · change cPayment 1790 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1790+point (1327/200) 4096 1791)/2)
    have hp : cPayment 1790 = (74264286556:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1790+point (1327/200) 4096 1791)/2 = (5163987:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1790
  · change cPayment 1791 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1791+point (1327/200) 4096 1792)/2)
    have hp : cPayment 1791 = (74240416512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1791+point (1327/200) 4096 1792)/2 = (5165041:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1791
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_111
