import WR2ClassicalCPayments
import WR2ClassicalCPoints252
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_252 (j : Fin 16) : cPayment (16*252+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*252+j.val)+point (1327/200) 4096 (16*252+j.val+1))/2) := by
  fin_cases j
  · change cPayment 4032 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4032+point (1327/200) 4096 4033)/2)
    have hp : cPayment 4032 = (2026045604:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4032+point (1327/200) 4096 4033)/2 = (1505411:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4032
  · change cPayment 4033 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4033+point (1327/200) 4096 4034)/2)
    have hp : cPayment 4033 = (1994024602:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4033+point (1327/200) 4096 4034)/2 = (7528109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4033
  · change cPayment 4034 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4034+point (1327/200) 4096 4035)/2)
    have hp : cPayment 4034 = (1962007241:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4034+point (1327/200) 4096 4035)/2 = (7529163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4034
  · change cPayment 4035 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4035+point (1327/200) 4096 4036)/2)
    have hp : cPayment 4035 = (1929993522:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4035+point (1327/200) 4096 4036)/2 = (7530217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4035
  · change cPayment 4036 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4036+point (1327/200) 4096 4037)/2)
    have hp : cPayment 4036 = (1897983447:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4036+point (1327/200) 4096 4037)/2 = (7531271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4036
  · change cPayment 4037 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4037+point (1327/200) 4096 4038)/2)
    have hp : cPayment 4037 = (1865977018:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4037+point (1327/200) 4096 4038)/2 = (301293:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4037
  · change cPayment 4038 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4038+point (1327/200) 4096 4039)/2)
    have hp : cPayment 4038 = (1833974237:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4038+point (1327/200) 4096 4039)/2 = (7533379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4038
  · change cPayment 4039 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4039+point (1327/200) 4096 4040)/2)
    have hp : cPayment 4039 = (1801975104:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4039+point (1327/200) 4096 4040)/2 = (7534433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4039
  · change cPayment 4040 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4040+point (1327/200) 4096 4041)/2)
    have hp : cPayment 4040 = (1769979622:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4040+point (1327/200) 4096 4041)/2 = (7535487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4040
  · change cPayment 4041 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4041+point (1327/200) 4096 4042)/2)
    have hp : cPayment 4041 = (1737987792:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4041+point (1327/200) 4096 4042)/2 = (7536541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4041
  · change cPayment 4042 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4042+point (1327/200) 4096 4043)/2)
    have hp : cPayment 4042 = (1705999615:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4042+point (1327/200) 4096 4043)/2 = (1507519:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4042
  · change cPayment 4043 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4043+point (1327/200) 4096 4044)/2)
    have hp : cPayment 4043 = (1674015094:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4043+point (1327/200) 4096 4044)/2 = (7538649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4043
  · change cPayment 4044 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4044+point (1327/200) 4096 4045)/2)
    have hp : cPayment 4044 = (1642034229:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4044+point (1327/200) 4096 4045)/2 = (7539703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4044
  · change cPayment 4045 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4045+point (1327/200) 4096 4046)/2)
    have hp : cPayment 4045 = (1610057023:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4045+point (1327/200) 4096 4046)/2 = (7540757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4045
  · change cPayment 4046 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4046+point (1327/200) 4096 4047)/2)
    have hp : cPayment 4046 = (1578083476:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4046+point (1327/200) 4096 4047)/2 = (7541811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4046
  · change cPayment 4047 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4047+point (1327/200) 4096 4048)/2)
    have hp : cPayment 4047 = (1546113591:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4047+point (1327/200) 4096 4048)/2 = (1508573:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4047
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_252
