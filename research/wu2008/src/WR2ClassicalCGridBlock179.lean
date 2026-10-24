import WR2ClassicalCPayments
import WR2ClassicalCPoints179
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_179 (j : Fin 16) : cPayment (16*179+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*179+j.val)+point (1327/200) 4096 (16*179+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2864 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2864+point (1327/200) 4096 2865)/2)
    have hp : cPayment 2864 = (41193242699:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2864+point (1327/200) 4096 2865)/2 = (6295983:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2864
  · change cPayment 2865 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2865+point (1327/200) 4096 2866)/2)
    have hp : cPayment 2865 = (41159151670:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2865+point (1327/200) 4096 2866)/2 = (6297037:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2865
  · change cPayment 2866 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2866+point (1327/200) 4096 2867)/2)
    have hp : cPayment 2866 = (41125059196:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2866+point (1327/200) 4096 2867)/2 = (6298091:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2866
  · change cPayment 2867 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2867+point (1327/200) 4096 2868)/2)
    have hp : cPayment 2867 = (41090965286:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2867+point (1327/200) 4096 2868)/2 = (1259829:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2867
  · change cPayment 2868 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2868+point (1327/200) 4096 2869)/2)
    have hp : cPayment 2868 = (41056869951:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2868+point (1327/200) 4096 2869)/2 = (6300199:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2868
  · change cPayment 2869 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2869+point (1327/200) 4096 2870)/2)
    have hp : cPayment 2869 = (41022773197:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2869+point (1327/200) 4096 2870)/2 = (6301253:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2869
  · change cPayment 2870 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2870+point (1327/200) 4096 2871)/2)
    have hp : cPayment 2870 = (40988675033:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2870+point (1327/200) 4096 2871)/2 = (6302307:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2870
  · change cPayment 2871 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2871+point (1327/200) 4096 2872)/2)
    have hp : cPayment 2871 = (40954575470:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2871+point (1327/200) 4096 2872)/2 = (6303361:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2871
  · change cPayment 2872 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2872+point (1327/200) 4096 2873)/2)
    have hp : cPayment 2872 = (40920474514:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2872+point (1327/200) 4096 2873)/2 = (1260883:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2872
  · change cPayment 2873 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2873+point (1327/200) 4096 2874)/2)
    have hp : cPayment 2873 = (40886372176:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2873+point (1327/200) 4096 2874)/2 = (6305469:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2873
  · change cPayment 2874 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2874+point (1327/200) 4096 2875)/2)
    have hp : cPayment 2874 = (40852268463:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2874+point (1327/200) 4096 2875)/2 = (6306523:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2874
  · change cPayment 2875 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2875+point (1327/200) 4096 2876)/2)
    have hp : cPayment 2875 = (40818163384:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2875+point (1327/200) 4096 2876)/2 = (6307577:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2875
  · change cPayment 2876 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2876+point (1327/200) 4096 2877)/2)
    have hp : cPayment 2876 = (40784056949:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2876+point (1327/200) 4096 2877)/2 = (6308631:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2876
  · change cPayment 2877 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2877+point (1327/200) 4096 2878)/2)
    have hp : cPayment 2877 = (40749949165:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2877+point (1327/200) 4096 2878)/2 = (1261937:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2877
  · change cPayment 2878 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2878+point (1327/200) 4096 2879)/2)
    have hp : cPayment 2878 = (40715840042:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2878+point (1327/200) 4096 2879)/2 = (6310739:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2878
  · change cPayment 2879 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2879+point (1327/200) 4096 2880)/2)
    have hp : cPayment 2879 = (40681729587:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2879+point (1327/200) 4096 2880)/2 = (6311793:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2879
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_179
