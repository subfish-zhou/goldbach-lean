import WR2ClassicalCPayments
import WR2ClassicalCPoints073
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_073 (j : Fin 16) : cPayment (16*73+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*73+j.val)+point (1327/200) 4096 (16*73+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1168 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1168+point (1327/200) 4096 1169)/2)
    have hp : cPayment 1168 = (82872407357:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1168+point (1327/200) 4096 1169)/2 = (4508399:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1168
  · change cPayment 1169 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1169+point (1327/200) 4096 1170)/2)
    have hp : cPayment 1169 = (82872360439:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1169+point (1327/200) 4096 1170)/2 = (4509453:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1169
  · change cPayment 1170 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1170+point (1327/200) 4096 1171)/2)
    have hp : cPayment 1170 = (82872253902:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1170+point (1327/200) 4096 1171)/2 = (4510507:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1170
  · change cPayment 1171 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1171+point (1327/200) 4096 1172)/2)
    have hp : cPayment 1171 = (82872087838:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1171+point (1327/200) 4096 1172)/2 = (4511561:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1171
  · change cPayment 1172 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1172+point (1327/200) 4096 1173)/2)
    have hp : cPayment 1172 = (82871862339:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1172+point (1327/200) 4096 1173)/2 = (902523:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1172
  · change cPayment 1173 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1173+point (1327/200) 4096 1174)/2)
    have hp : cPayment 1173 = (82871577494:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1173+point (1327/200) 4096 1174)/2 = (4513669:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1173
  · change cPayment 1174 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1174+point (1327/200) 4096 1175)/2)
    have hp : cPayment 1174 = (82871233395:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1174+point (1327/200) 4096 1175)/2 = (4514723:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1174
  · change cPayment 1175 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1175+point (1327/200) 4096 1176)/2)
    have hp : cPayment 1175 = (82870830133:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1175+point (1327/200) 4096 1176)/2 = (4515777:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1175
  · change cPayment 1176 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1176+point (1327/200) 4096 1177)/2)
    have hp : cPayment 1176 = (82870367797:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1176+point (1327/200) 4096 1177)/2 = (4516831:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1176
  · change cPayment 1177 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1177+point (1327/200) 4096 1178)/2)
    have hp : cPayment 1177 = (82869846480:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1177+point (1327/200) 4096 1178)/2 = (903577:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1177
  · change cPayment 1178 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1178+point (1327/200) 4096 1179)/2)
    have hp : cPayment 1178 = (82869266269:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1178+point (1327/200) 4096 1179)/2 = (4518939:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1178
  · change cPayment 1179 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1179+point (1327/200) 4096 1180)/2)
    have hp : cPayment 1179 = (82868627257:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1179+point (1327/200) 4096 1180)/2 = (4519993:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1179
  · change cPayment 1180 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1180+point (1327/200) 4096 1181)/2)
    have hp : cPayment 1180 = (82867929533:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1180+point (1327/200) 4096 1181)/2 = (4521047:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1180
  · change cPayment 1181 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1181+point (1327/200) 4096 1182)/2)
    have hp : cPayment 1181 = (82867173187:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1181+point (1327/200) 4096 1182)/2 = (4522101:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1181
  · change cPayment 1182 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1182+point (1327/200) 4096 1183)/2)
    have hp : cPayment 1182 = (82866358308:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1182+point (1327/200) 4096 1183)/2 = (904631:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1182
  · change cPayment 1183 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1183+point (1327/200) 4096 1184)/2)
    have hp : cPayment 1183 = (82865484986:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1183+point (1327/200) 4096 1184)/2 = (4524209:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1183
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_073
