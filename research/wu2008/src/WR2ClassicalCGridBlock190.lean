import WR2ClassicalCPayments
import WR2ClassicalCPoints190
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_190 (j : Fin 16) : cPayment (16*190+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*190+j.val)+point (1327/200) 4096 (16*190+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3040 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3040+point (1327/200) 4096 3041)/2)
    have hp : cPayment 3040 = (35178389308:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3040+point (1327/200) 4096 3041)/2 = (6481487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3040
  · change cPayment 3041 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3041+point (1327/200) 4096 3042)/2)
    have hp : cPayment 3041 = (35144169404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3041+point (1327/200) 4096 3042)/2 = (6482541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3041
  · change cPayment 3042 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3042+point (1327/200) 4096 3043)/2)
    have hp : cPayment 3042 = (35109949434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3042+point (1327/200) 4096 3043)/2 = (1296719:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3042
  · change cPayment 3043 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3043+point (1327/200) 4096 3044)/2)
    have hp : cPayment 3043 = (35075729404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3043+point (1327/200) 4096 3044)/2 = (6484649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3043
  · change cPayment 3044 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3044+point (1327/200) 4096 3045)/2)
    have hp : cPayment 3044 = (35041509322:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3044+point (1327/200) 4096 3045)/2 = (6485703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3044
  · change cPayment 3045 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3045+point (1327/200) 4096 3046)/2)
    have hp : cPayment 3045 = (35007289194:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3045+point (1327/200) 4096 3046)/2 = (6486757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3045
  · change cPayment 3046 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3046+point (1327/200) 4096 3047)/2)
    have hp : cPayment 3046 = (34973069028:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3046+point (1327/200) 4096 3047)/2 = (6487811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3046
  · change cPayment 3047 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3047+point (1327/200) 4096 3048)/2)
    have hp : cPayment 3047 = (34938848829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3047+point (1327/200) 4096 3048)/2 = (1297773:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3047
  · change cPayment 3048 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3048+point (1327/200) 4096 3049)/2)
    have hp : cPayment 3048 = (34904628606:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3048+point (1327/200) 4096 3049)/2 = (6489919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3048
  · change cPayment 3049 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3049+point (1327/200) 4096 3050)/2)
    have hp : cPayment 3049 = (34870408364:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3049+point (1327/200) 4096 3050)/2 = (6490973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3049
  · change cPayment 3050 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3050+point (1327/200) 4096 3051)/2)
    have hp : cPayment 3050 = (34836188111:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3050+point (1327/200) 4096 3051)/2 = (6492027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3050
  · change cPayment 3051 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3051+point (1327/200) 4096 3052)/2)
    have hp : cPayment 3051 = (34801967854:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3051+point (1327/200) 4096 3052)/2 = (6493081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3051
  · change cPayment 3052 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3052+point (1327/200) 4096 3053)/2)
    have hp : cPayment 3052 = (34767747599:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3052+point (1327/200) 4096 3053)/2 = (1298827:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3052
  · change cPayment 3053 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3053+point (1327/200) 4096 3054)/2)
    have hp : cPayment 3053 = (34733527354:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3053+point (1327/200) 4096 3054)/2 = (6495189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3053
  · change cPayment 3054 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3054+point (1327/200) 4096 3055)/2)
    have hp : cPayment 3054 = (34699307124:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3054+point (1327/200) 4096 3055)/2 = (6496243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3054
  · change cPayment 3055 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3055+point (1327/200) 4096 3056)/2)
    have hp : cPayment 3055 = (34665086918:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3055+point (1327/200) 4096 3056)/2 = (6497297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3055
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_190
