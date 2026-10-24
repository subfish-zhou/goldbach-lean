import WR2ClassicalCPayments
import WR2ClassicalCPoints054
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_054 (j : Fin 16) : cPayment (16*54+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*54+j.val)+point (1327/200) 4096 (16*54+j.val+1))/2) := by
  fin_cases j
  · change cPayment 864 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 864+point (1327/200) 4096 865)/2)
    have hp : cPayment 864 = (79634994717:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 864+point (1327/200) 4096 865)/2 = (4187983:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_864
  · change cPayment 865 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 865+point (1327/200) 4096 866)/2)
    have hp : cPayment 865 = (79658056461:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 865+point (1327/200) 4096 866)/2 = (4189037:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_865
  · change cPayment 866 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 866+point (1327/200) 4096 867)/2)
    have hp : cPayment 866 = (79681023092:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 866+point (1327/200) 4096 867)/2 = (4190091:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_866
  · change cPayment 867 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 867+point (1327/200) 4096 868)/2)
    have hp : cPayment 867 = (79703894756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 867+point (1327/200) 4096 868)/2 = (838229:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_867
  · change cPayment 868 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 868+point (1327/200) 4096 869)/2)
    have hp : cPayment 868 = (79726671601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 868+point (1327/200) 4096 869)/2 = (4192199:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_868
  · change cPayment 869 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 869+point (1327/200) 4096 870)/2)
    have hp : cPayment 869 = (79749353774:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 869+point (1327/200) 4096 870)/2 = (4193253:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_869
  · change cPayment 870 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 870+point (1327/200) 4096 871)/2)
    have hp : cPayment 870 = (79771941420:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 870+point (1327/200) 4096 871)/2 = (4194307:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_870
  · change cPayment 871 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 871+point (1327/200) 4096 872)/2)
    have hp : cPayment 871 = (79794434685:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 871+point (1327/200) 4096 872)/2 = (4195361:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_871
  · change cPayment 872 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 872+point (1327/200) 4096 873)/2)
    have hp : cPayment 872 = (79816833717:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 872+point (1327/200) 4096 873)/2 = (839283:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_872
  · change cPayment 873 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 873+point (1327/200) 4096 874)/2)
    have hp : cPayment 873 = (79839138660:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 873+point (1327/200) 4096 874)/2 = (4197469:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_873
  · change cPayment 874 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 874+point (1327/200) 4096 875)/2)
    have hp : cPayment 874 = (79861349660:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 874+point (1327/200) 4096 875)/2 = (4198523:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_874
  · change cPayment 875 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 875+point (1327/200) 4096 876)/2)
    have hp : cPayment 875 = (79883466862:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 875+point (1327/200) 4096 876)/2 = (4199577:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_875
  · change cPayment 876 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 876+point (1327/200) 4096 877)/2)
    have hp : cPayment 876 = (79905490411:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 876+point (1327/200) 4096 877)/2 = (4200631:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_876
  · change cPayment 877 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 877+point (1327/200) 4096 878)/2)
    have hp : cPayment 877 = (79927420452:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 877+point (1327/200) 4096 878)/2 = (840337:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_877
  · change cPayment 878 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 878+point (1327/200) 4096 879)/2)
    have hp : cPayment 878 = (79949257129:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 878+point (1327/200) 4096 879)/2 = (4202739:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_878
  · change cPayment 879 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 879+point (1327/200) 4096 880)/2)
    have hp : cPayment 879 = (79971000587:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 879+point (1327/200) 4096 880)/2 = (4203793:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_879
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_054
