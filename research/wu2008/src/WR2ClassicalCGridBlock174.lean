import WR2ClassicalCPayments
import WR2ClassicalCPoints174
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_174 (j : Fin 16) : cPayment (16*174+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*174+j.val)+point (1327/200) 4096 (16*174+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2784 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2784+point (1327/200) 4096 2785)/2)
    have hp : cPayment 2784 = (43915046122:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2784+point (1327/200) 4096 2785)/2 = (6211663:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2784
  · change cPayment 2785 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2785+point (1327/200) 4096 2786)/2)
    have hp : cPayment 2785 = (43881100144:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2785+point (1327/200) 4096 2786)/2 = (6212717:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2785
  · change cPayment 2786 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2786+point (1327/200) 4096 2787)/2)
    have hp : cPayment 2786 = (43847151981:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2786+point (1327/200) 4096 2787)/2 = (6213771:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2786
  · change cPayment 2787 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2787+point (1327/200) 4096 2788)/2)
    have hp : cPayment 2787 = (43813201642:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2787+point (1327/200) 4096 2788)/2 = (248593:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2787
  · change cPayment 2788 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2788+point (1327/200) 4096 2789)/2)
    have hp : cPayment 2788 = (43779249136:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2788+point (1327/200) 4096 2789)/2 = (6215879:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2788
  · change cPayment 2789 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2789+point (1327/200) 4096 2790)/2)
    have hp : cPayment 2789 = (43745294473:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2789+point (1327/200) 4096 2790)/2 = (6216933:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2789
  · change cPayment 2790 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2790+point (1327/200) 4096 2791)/2)
    have hp : cPayment 2790 = (43711337664:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2790+point (1327/200) 4096 2791)/2 = (6217987:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2790
  · change cPayment 2791 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2791+point (1327/200) 4096 2792)/2)
    have hp : cPayment 2791 = (43677378717:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2791+point (1327/200) 4096 2792)/2 = (6219041:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2791
  · change cPayment 2792 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2792+point (1327/200) 4096 2793)/2)
    have hp : cPayment 2792 = (43643417643:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2792+point (1327/200) 4096 2793)/2 = (1244019:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2792
  · change cPayment 2793 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2793+point (1327/200) 4096 2794)/2)
    have hp : cPayment 2793 = (43609454451:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2793+point (1327/200) 4096 2794)/2 = (6221149:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2793
  · change cPayment 2794 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2794+point (1327/200) 4096 2795)/2)
    have hp : cPayment 2794 = (43575489150:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2794+point (1327/200) 4096 2795)/2 = (6222203:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2794
  · change cPayment 2795 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2795+point (1327/200) 4096 2796)/2)
    have hp : cPayment 2795 = (43541521752:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2795+point (1327/200) 4096 2796)/2 = (6223257:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2795
  · change cPayment 2796 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2796+point (1327/200) 4096 2797)/2)
    have hp : cPayment 2796 = (43507552264:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2796+point (1327/200) 4096 2797)/2 = (6224311:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2796
  · change cPayment 2797 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2797+point (1327/200) 4096 2798)/2)
    have hp : cPayment 2797 = (43473580698:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2797+point (1327/200) 4096 2798)/2 = (1245073:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2797
  · change cPayment 2798 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2798+point (1327/200) 4096 2799)/2)
    have hp : cPayment 2798 = (43439607061:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2798+point (1327/200) 4096 2799)/2 = (6226419:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2798
  · change cPayment 2799 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2799+point (1327/200) 4096 2800)/2)
    have hp : cPayment 2799 = (43405631365:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2799+point (1327/200) 4096 2800)/2 = (6227473:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2799
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_174
