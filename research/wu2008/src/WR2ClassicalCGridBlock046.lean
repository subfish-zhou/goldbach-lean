import WR2ClassicalCPayments
import WR2ClassicalCPoints046
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_046 (j : Fin 16) : cPayment (16*46+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*46+j.val)+point (1327/200) 4096 (16*46+j.val+1))/2) := by
  fin_cases j
  · change cPayment 736 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 736+point (1327/200) 4096 737)/2)
    have hp : cPayment 736 = (75842257518:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 736+point (1327/200) 4096 737)/2 = (4053071:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_736
  · change cPayment 737 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 737+point (1327/200) 4096 738)/2)
    have hp : cPayment 737 = (75878799392:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 737+point (1327/200) 4096 738)/2 = (162165:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_737
  · change cPayment 738 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 738+point (1327/200) 4096 739)/2)
    have hp : cPayment 738 = (75915225177:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 738+point (1327/200) 4096 739)/2 = (4055179:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_738
  · change cPayment 739 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 739+point (1327/200) 4096 740)/2)
    have hp : cPayment 739 = (75951535056:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 739+point (1327/200) 4096 740)/2 = (4056233:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_739
  · change cPayment 740 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 740+point (1327/200) 4096 741)/2)
    have hp : cPayment 740 = (75987729211:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 740+point (1327/200) 4096 741)/2 = (4057287:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_740
  · change cPayment 741 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 741+point (1327/200) 4096 742)/2)
    have hp : cPayment 741 = (76023807822:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 741+point (1327/200) 4096 742)/2 = (4058341:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_741
  · change cPayment 742 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 742+point (1327/200) 4096 743)/2)
    have hp : cPayment 742 = (76059771071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 742+point (1327/200) 4096 743)/2 = (811879:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_742
  · change cPayment 743 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 743+point (1327/200) 4096 744)/2)
    have hp : cPayment 743 = (76095619137:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 743+point (1327/200) 4096 744)/2 = (4060449:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_743
  · change cPayment 744 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 744+point (1327/200) 4096 745)/2)
    have hp : cPayment 744 = (76131352202:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 744+point (1327/200) 4096 745)/2 = (4061503:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_744
  · change cPayment 745 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 745+point (1327/200) 4096 746)/2)
    have hp : cPayment 745 = (76166970444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 745+point (1327/200) 4096 746)/2 = (4062557:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_745
  · change cPayment 746 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 746+point (1327/200) 4096 747)/2)
    have hp : cPayment 746 = (76202474044:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 746+point (1327/200) 4096 747)/2 = (4063611:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_746
  · change cPayment 747 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 747+point (1327/200) 4096 748)/2)
    have hp : cPayment 747 = (76237863181:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 747+point (1327/200) 4096 748)/2 = (812933:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_747
  · change cPayment 748 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 748+point (1327/200) 4096 749)/2)
    have hp : cPayment 748 = (76273138034:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 748+point (1327/200) 4096 749)/2 = (4065719:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_748
  · change cPayment 749 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 749+point (1327/200) 4096 750)/2)
    have hp : cPayment 749 = (76308298781:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 749+point (1327/200) 4096 750)/2 = (4066773:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_749
  · change cPayment 750 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 750+point (1327/200) 4096 751)/2)
    have hp : cPayment 750 = (76343345602:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 750+point (1327/200) 4096 751)/2 = (4067827:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_750
  · change cPayment 751 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 751+point (1327/200) 4096 752)/2)
    have hp : cPayment 751 = (76378278673:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 751+point (1327/200) 4096 752)/2 = (4068881:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_751
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_046
