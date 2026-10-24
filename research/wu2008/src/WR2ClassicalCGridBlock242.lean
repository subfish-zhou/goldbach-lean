import WR2ClassicalCPayments
import WR2ClassicalCPoints242
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_242 (j : Fin 16) : cPayment (16*242+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*242+j.val)+point (1327/200) 4096 (16*242+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3872 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3872+point (1327/200) 4096 3873)/2)
    have hp : cPayment 3872 = (7195114201:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3872+point (1327/200) 4096 3873)/2 = (1471683:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3872
  · change cPayment 3873 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3873+point (1327/200) 4096 3874)/2)
    have hp : cPayment 3873 = (7162533147:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3873+point (1327/200) 4096 3874)/2 = (7359469:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3873
  · change cPayment 3874 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3874+point (1327/200) 4096 3875)/2)
    have hp : cPayment 3874 = (7129955442:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3874+point (1327/200) 4096 3875)/2 = (7360523:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3874
  · change cPayment 3875 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3875+point (1327/200) 4096 3876)/2)
    have hp : cPayment 3875 = (7097381088:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3875+point (1327/200) 4096 3876)/2 = (7361577:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3875
  · change cPayment 3876 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3876+point (1327/200) 4096 3877)/2)
    have hp : cPayment 3876 = (7064810086:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3876+point (1327/200) 4096 3877)/2 = (7362631:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3876
  · change cPayment 3877 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3877+point (1327/200) 4096 3878)/2)
    have hp : cPayment 3877 = (7032242438:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3877+point (1327/200) 4096 3878)/2 = (1472737:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3877
  · change cPayment 3878 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3878+point (1327/200) 4096 3879)/2)
    have hp : cPayment 3878 = (6999678148:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3878+point (1327/200) 4096 3879)/2 = (7364739:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3878
  · change cPayment 3879 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3879+point (1327/200) 4096 3880)/2)
    have hp : cPayment 3879 = (6967117216:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3879+point (1327/200) 4096 3880)/2 = (7365793:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3879
  · change cPayment 3880 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3880+point (1327/200) 4096 3881)/2)
    have hp : cPayment 3880 = (6934559645:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3880+point (1327/200) 4096 3881)/2 = (7366847:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3880
  · change cPayment 3881 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3881+point (1327/200) 4096 3882)/2)
    have hp : cPayment 3881 = (6902005436:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3881+point (1327/200) 4096 3882)/2 = (7367901:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3881
  · change cPayment 3882 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3882+point (1327/200) 4096 3883)/2)
    have hp : cPayment 3882 = (6869454593:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3882+point (1327/200) 4096 3883)/2 = (1473791:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3882
  · change cPayment 3883 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3883+point (1327/200) 4096 3884)/2)
    have hp : cPayment 3883 = (6836907117:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3883+point (1327/200) 4096 3884)/2 = (7370009:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3883
  · change cPayment 3884 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3884+point (1327/200) 4096 3885)/2)
    have hp : cPayment 3884 = (6804363010:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3884+point (1327/200) 4096 3885)/2 = (7371063:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3884
  · change cPayment 3885 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3885+point (1327/200) 4096 3886)/2)
    have hp : cPayment 3885 = (6771822274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3885+point (1327/200) 4096 3886)/2 = (7372117:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3885
  · change cPayment 3886 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3886+point (1327/200) 4096 3887)/2)
    have hp : cPayment 3886 = (6739284911:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3886+point (1327/200) 4096 3887)/2 = (7373171:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3886
  · change cPayment 3887 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3887+point (1327/200) 4096 3888)/2)
    have hp : cPayment 3887 = (6706750924:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3887+point (1327/200) 4096 3888)/2 = (294969:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3887
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_242
