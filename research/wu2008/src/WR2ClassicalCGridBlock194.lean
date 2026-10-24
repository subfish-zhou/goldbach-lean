import WR2ClassicalCPayments
import WR2ClassicalCPoints194
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_194 (j : Fin 16) : cPayment (16*194+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*194+j.val)+point (1327/200) 4096 (16*194+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3104 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3104+point (1327/200) 4096 3105)/2)
    have hp : cPayment 3104 = (32988464598:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3104+point (1327/200) 4096 3105)/2 = (6548943:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3104
  · change cPayment 3105 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3105+point (1327/200) 4096 3106)/2)
    have hp : cPayment 3105 = (32954254041:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3105+point (1327/200) 4096 3106)/2 = (6549997:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3105
  · change cPayment 3106 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3106+point (1327/200) 4096 3107)/2)
    have hp : cPayment 3106 = (32920043842:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3106+point (1327/200) 4096 3107)/2 = (6551051:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3106
  · change cPayment 3107 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3107+point (1327/200) 4096 3108)/2)
    have hp : cPayment 3107 = (32885834010:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3107+point (1327/200) 4096 3108)/2 = (1310421:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3107
  · change cPayment 3108 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3108+point (1327/200) 4096 3109)/2)
    have hp : cPayment 3108 = (32851624548:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3108+point (1327/200) 4096 3109)/2 = (6553159:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3108
  · change cPayment 3109 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3109+point (1327/200) 4096 3110)/2)
    have hp : cPayment 3109 = (32817415465:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3109+point (1327/200) 4096 3110)/2 = (6554213:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3109
  · change cPayment 3110 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3110+point (1327/200) 4096 3111)/2)
    have hp : cPayment 3110 = (32783206767:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3110+point (1327/200) 4096 3111)/2 = (6555267:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3110
  · change cPayment 3111 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3111+point (1327/200) 4096 3112)/2)
    have hp : cPayment 3111 = (32748998459:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3111+point (1327/200) 4096 3112)/2 = (6556321:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3111
  · change cPayment 3112 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3112+point (1327/200) 4096 3113)/2)
    have hp : cPayment 3112 = (32714790548:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3112+point (1327/200) 4096 3113)/2 = (262295:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3112
  · change cPayment 3113 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3113+point (1327/200) 4096 3114)/2)
    have hp : cPayment 3113 = (32680583041:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3113+point (1327/200) 4096 3114)/2 = (6558429:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3113
  · change cPayment 3114 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3114+point (1327/200) 4096 3115)/2)
    have hp : cPayment 3114 = (32646375943:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3114+point (1327/200) 4096 3115)/2 = (6559483:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3114
  · change cPayment 3115 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3115+point (1327/200) 4096 3116)/2)
    have hp : cPayment 3115 = (32612169262:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3115+point (1327/200) 4096 3116)/2 = (6560537:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3115
  · change cPayment 3116 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3116+point (1327/200) 4096 3117)/2)
    have hp : cPayment 3116 = (32577963002:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3116+point (1327/200) 4096 3117)/2 = (6561591:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3116
  · change cPayment 3117 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3117+point (1327/200) 4096 3118)/2)
    have hp : cPayment 3117 = (32543757171:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3117+point (1327/200) 4096 3118)/2 = (1312529:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3117
  · change cPayment 3118 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3118+point (1327/200) 4096 3119)/2)
    have hp : cPayment 3118 = (32509551775:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3118+point (1327/200) 4096 3119)/2 = (6563699:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3118
  · change cPayment 3119 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3119+point (1327/200) 4096 3120)/2)
    have hp : cPayment 3119 = (32475346820:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3119+point (1327/200) 4096 3120)/2 = (6564753:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3119
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_194
