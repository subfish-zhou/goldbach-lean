import WR2ClassicalCPayments
import WR2ClassicalCPoints112
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_112 (j : Fin 16) : cPayment (16*112+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*112+j.val)+point (1327/200) 4096 (16*112+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1792 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1792+point (1327/200) 4096 1793)/2)
    have hp : cPayment 1792 = (74216524026:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1792+point (1327/200) 4096 1793)/2 = (1033219:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1792
  · change cPayment 1793 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1793+point (1327/200) 4096 1794)/2)
    have hp : cPayment 1793 = (74192609136:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1793+point (1327/200) 4096 1794)/2 = (5167149:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1793
  · change cPayment 1794 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1794+point (1327/200) 4096 1795)/2)
    have hp : cPayment 1794 = (74168671879:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1794+point (1327/200) 4096 1795)/2 = (5168203:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1794
  · change cPayment 1795 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1795+point (1327/200) 4096 1796)/2)
    have hp : cPayment 1795 = (74144712291:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1795+point (1327/200) 4096 1796)/2 = (5169257:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1795
  · change cPayment 1796 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1796+point (1327/200) 4096 1797)/2)
    have hp : cPayment 1796 = (74120730411:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1796+point (1327/200) 4096 1797)/2 = (5170311:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1796
  · change cPayment 1797 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1797+point (1327/200) 4096 1798)/2)
    have hp : cPayment 1797 = (74096726274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1797+point (1327/200) 4096 1798)/2 = (1034273:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1797
  · change cPayment 1798 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1798+point (1327/200) 4096 1799)/2)
    have hp : cPayment 1798 = (74072699918:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1798+point (1327/200) 4096 1799)/2 = (5172419:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1798
  · change cPayment 1799 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1799+point (1327/200) 4096 1800)/2)
    have hp : cPayment 1799 = (74048651379:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1799+point (1327/200) 4096 1800)/2 = (5173473:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1799
  · change cPayment 1800 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1800+point (1327/200) 4096 1801)/2)
    have hp : cPayment 1800 = (74024580694:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1800+point (1327/200) 4096 1801)/2 = (5174527:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1800
  · change cPayment 1801 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1801+point (1327/200) 4096 1802)/2)
    have hp : cPayment 1801 = (74000487900:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1801+point (1327/200) 4096 1802)/2 = (5175581:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1801
  · change cPayment 1802 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1802+point (1327/200) 4096 1803)/2)
    have hp : cPayment 1802 = (73976373033:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1802+point (1327/200) 4096 1803)/2 = (1035327:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1802
  · change cPayment 1803 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1803+point (1327/200) 4096 1804)/2)
    have hp : cPayment 1803 = (73952236129:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1803+point (1327/200) 4096 1804)/2 = (5177689:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1803
  · change cPayment 1804 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1804+point (1327/200) 4096 1805)/2)
    have hp : cPayment 1804 = (73928077226:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1804+point (1327/200) 4096 1805)/2 = (5178743:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1804
  · change cPayment 1805 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1805+point (1327/200) 4096 1806)/2)
    have hp : cPayment 1805 = (73903896360:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1805+point (1327/200) 4096 1806)/2 = (5179797:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1805
  · change cPayment 1806 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1806+point (1327/200) 4096 1807)/2)
    have hp : cPayment 1806 = (73879693567:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1806+point (1327/200) 4096 1807)/2 = (5180851:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1806
  · change cPayment 1807 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1807+point (1327/200) 4096 1808)/2)
    have hp : cPayment 1807 = (73855468883:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1807+point (1327/200) 4096 1808)/2 = (1036381:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1807
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_112
