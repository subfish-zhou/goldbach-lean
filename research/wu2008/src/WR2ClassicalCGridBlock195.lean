import WR2ClassicalCPayments
import WR2ClassicalCPoints195
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_195 (j : Fin 16) : cPayment (16*195+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*195+j.val)+point (1327/200) 4096 (16*195+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3120 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3120+point (1327/200) 4096 3121)/2)
    have hp : cPayment 3120 = (32441142313:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3120+point (1327/200) 4096 3121)/2 = (6565807:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3120
  · change cPayment 3121 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3121+point (1327/200) 4096 3122)/2)
    have hp : cPayment 3121 = (32406938259:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3121+point (1327/200) 4096 3122)/2 = (6566861:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3121
  · change cPayment 3122 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3122+point (1327/200) 4096 3123)/2)
    have hp : cPayment 3122 = (32372734664:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3122+point (1327/200) 4096 3123)/2 = (1313583:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3122
  · change cPayment 3123 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3123+point (1327/200) 4096 3124)/2)
    have hp : cPayment 3123 = (32338531536:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3123+point (1327/200) 4096 3124)/2 = (6568969:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3123
  · change cPayment 3124 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3124+point (1327/200) 4096 3125)/2)
    have hp : cPayment 3124 = (32304328880:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3124+point (1327/200) 4096 3125)/2 = (6570023:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3124
  · change cPayment 3125 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3125+point (1327/200) 4096 3126)/2)
    have hp : cPayment 3125 = (32270126702:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3125+point (1327/200) 4096 3126)/2 = (6571077:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3125
  · change cPayment 3126 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3126+point (1327/200) 4096 3127)/2)
    have hp : cPayment 3126 = (32235925009:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3126+point (1327/200) 4096 3127)/2 = (6572131:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3126
  · change cPayment 3127 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3127+point (1327/200) 4096 3128)/2)
    have hp : cPayment 3127 = (32201723807:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3127+point (1327/200) 4096 3128)/2 = (1314637:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3127
  · change cPayment 3128 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3128+point (1327/200) 4096 3129)/2)
    have hp : cPayment 3128 = (32167523102:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3128+point (1327/200) 4096 3129)/2 = (6574239:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3128
  · change cPayment 3129 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3129+point (1327/200) 4096 3130)/2)
    have hp : cPayment 3129 = (32133322900:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3129+point (1327/200) 4096 3130)/2 = (6575293:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3129
  · change cPayment 3130 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3130+point (1327/200) 4096 3131)/2)
    have hp : cPayment 3130 = (32099123207:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3130+point (1327/200) 4096 3131)/2 = (6576347:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3130
  · change cPayment 3131 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3131+point (1327/200) 4096 3132)/2)
    have hp : cPayment 3131 = (32064924030:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3131+point (1327/200) 4096 3132)/2 = (6577401:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3131
  · change cPayment 3132 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3132+point (1327/200) 4096 3133)/2)
    have hp : cPayment 3132 = (32030725374:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3132+point (1327/200) 4096 3133)/2 = (1315691:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3132
  · change cPayment 3133 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3133+point (1327/200) 4096 3134)/2)
    have hp : cPayment 3133 = (31996527247:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3133+point (1327/200) 4096 3134)/2 = (6579509:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3133
  · change cPayment 3134 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3134+point (1327/200) 4096 3135)/2)
    have hp : cPayment 3134 = (31962329653:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3134+point (1327/200) 4096 3135)/2 = (6580563:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3134
  · change cPayment 3135 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3135+point (1327/200) 4096 3136)/2)
    have hp : cPayment 3135 = (31928132599:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3135+point (1327/200) 4096 3136)/2 = (6581617:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3135
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_195
