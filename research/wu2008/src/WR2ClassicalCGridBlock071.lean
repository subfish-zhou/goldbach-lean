import WR2ClassicalCPayments
import WR2ClassicalCPoints071
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_071 (j : Fin 16) : cPayment (16*71+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*71+j.val)+point (1327/200) 4096 (16*71+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1136 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1136+point (1327/200) 4096 1137)/2)
    have hp : cPayment 1136 = (82841876907:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1136+point (1327/200) 4096 1137)/2 = (4474671:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1136
  · change cPayment 1137 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1137+point (1327/200) 4096 1138)/2)
    have hp : cPayment 1137 = (82843786796:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1137+point (1327/200) 4096 1138)/2 = (179029:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1137
  · change cPayment 1138 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1138+point (1327/200) 4096 1139)/2)
    have hp : cPayment 1138 = (82845634071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1138+point (1327/200) 4096 1139)/2 = (4476779:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1138
  · change cPayment 1139 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1139+point (1327/200) 4096 1140)/2)
    have hp : cPayment 1139 = (82847418829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1139+point (1327/200) 4096 1140)/2 = (4477833:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1139
  · change cPayment 1140 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1140+point (1327/200) 4096 1141)/2)
    have hp : cPayment 1140 = (82849141166:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1140+point (1327/200) 4096 1141)/2 = (4478887:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1140
  · change cPayment 1141 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1141+point (1327/200) 4096 1142)/2)
    have hp : cPayment 1141 = (82850801177:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1141+point (1327/200) 4096 1142)/2 = (4479941:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1141
  · change cPayment 1142 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1142+point (1327/200) 4096 1143)/2)
    have hp : cPayment 1142 = (82852398958:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1142+point (1327/200) 4096 1143)/2 = (896199:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1142
  · change cPayment 1143 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1143+point (1327/200) 4096 1144)/2)
    have hp : cPayment 1143 = (82853934603:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1143+point (1327/200) 4096 1144)/2 = (4482049:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1143
  · change cPayment 1144 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1144+point (1327/200) 4096 1145)/2)
    have hp : cPayment 1144 = (82855408208:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1144+point (1327/200) 4096 1145)/2 = (4483103:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1144
  · change cPayment 1145 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1145+point (1327/200) 4096 1146)/2)
    have hp : cPayment 1145 = (82856819868:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1145+point (1327/200) 4096 1146)/2 = (4484157:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1145
  · change cPayment 1146 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1146+point (1327/200) 4096 1147)/2)
    have hp : cPayment 1146 = (82858169677:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1146+point (1327/200) 4096 1147)/2 = (4485211:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1146
  · change cPayment 1147 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1147+point (1327/200) 4096 1148)/2)
    have hp : cPayment 1147 = (82859457731:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1147+point (1327/200) 4096 1148)/2 = (897253:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1147
  · change cPayment 1148 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1148+point (1327/200) 4096 1149)/2)
    have hp : cPayment 1148 = (82860684123:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1148+point (1327/200) 4096 1149)/2 = (4487319:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1148
  · change cPayment 1149 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1149+point (1327/200) 4096 1150)/2)
    have hp : cPayment 1149 = (82861848948:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1149+point (1327/200) 4096 1150)/2 = (4488373:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1149
  · change cPayment 1150 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1150+point (1327/200) 4096 1151)/2)
    have hp : cPayment 1150 = (82862952301:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1150+point (1327/200) 4096 1151)/2 = (4489427:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1150
  · change cPayment 1151 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1151+point (1327/200) 4096 1152)/2)
    have hp : cPayment 1151 = (82863994274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1151+point (1327/200) 4096 1152)/2 = (4490481:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1151
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_071
