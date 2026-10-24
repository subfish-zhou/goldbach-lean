import WR2ClassicalCPayments
import WR2ClassicalCPoints171
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_171 (j : Fin 16) : cPayment (16*171+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*171+j.val)+point (1327/200) 4096 (16*171+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2736 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2736+point (1327/200) 4096 2737)/2)
    have hp : cPayment 2736 = (45541687716:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2736+point (1327/200) 4096 2737)/2 = (6161071:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2736
  · change cPayment 2737 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2737+point (1327/200) 4096 2738)/2)
    have hp : cPayment 2737 = (45507858405:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2737+point (1327/200) 4096 2738)/2 = (246485:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2737
  · change cPayment 2738 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2738+point (1327/200) 4096 2739)/2)
    have hp : cPayment 2738 = (45474026424:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2738+point (1327/200) 4096 2739)/2 = (6163179:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2738
  · change cPayment 2739 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2739+point (1327/200) 4096 2740)/2)
    have hp : cPayment 2739 = (45440191783:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2739+point (1327/200) 4096 2740)/2 = (6164233:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2739
  · change cPayment 2740 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2740+point (1327/200) 4096 2741)/2)
    have hp : cPayment 2740 = (45406354493:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2740+point (1327/200) 4096 2741)/2 = (6165287:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2740
  · change cPayment 2741 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2741+point (1327/200) 4096 2742)/2)
    have hp : cPayment 2741 = (45372514564:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2741+point (1327/200) 4096 2742)/2 = (6166341:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2741
  · change cPayment 2742 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2742+point (1327/200) 4096 2743)/2)
    have hp : cPayment 2742 = (45338672005:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2742+point (1327/200) 4096 2743)/2 = (1233479:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2742
  · change cPayment 2743 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2743+point (1327/200) 4096 2744)/2)
    have hp : cPayment 2743 = (45304826829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2743+point (1327/200) 4096 2744)/2 = (6168449:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2743
  · change cPayment 2744 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2744+point (1327/200) 4096 2745)/2)
    have hp : cPayment 2744 = (45270979045:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2744+point (1327/200) 4096 2745)/2 = (6169503:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2744
  · change cPayment 2745 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2745+point (1327/200) 4096 2746)/2)
    have hp : cPayment 2745 = (45237128662:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2745+point (1327/200) 4096 2746)/2 = (6170557:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2745
  · change cPayment 2746 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2746+point (1327/200) 4096 2747)/2)
    have hp : cPayment 2746 = (45203275693:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2746+point (1327/200) 4096 2747)/2 = (6171611:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2746
  · change cPayment 2747 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2747+point (1327/200) 4096 2748)/2)
    have hp : cPayment 2747 = (45169420146:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2747+point (1327/200) 4096 2748)/2 = (1234533:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2747
  · change cPayment 2748 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2748+point (1327/200) 4096 2749)/2)
    have hp : cPayment 2748 = (45135562033:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2748+point (1327/200) 4096 2749)/2 = (6173719:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2748
  · change cPayment 2749 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2749+point (1327/200) 4096 2750)/2)
    have hp : cPayment 2749 = (45101701363:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2749+point (1327/200) 4096 2750)/2 = (6174773:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2749
  · change cPayment 2750 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2750+point (1327/200) 4096 2751)/2)
    have hp : cPayment 2750 = (45067838147:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2750+point (1327/200) 4096 2751)/2 = (6175827:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2750
  · change cPayment 2751 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2751+point (1327/200) 4096 2752)/2)
    have hp : cPayment 2751 = (45033972395:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2751+point (1327/200) 4096 2752)/2 = (6176881:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2751
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_171
