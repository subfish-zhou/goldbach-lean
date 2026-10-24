import WR2ClassicalCPayments
import WR2ClassicalCPoints072
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_072 (j : Fin 16) : cPayment (16*72+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*72+j.val)+point (1327/200) 4096 (16*72+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1152 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1152+point (1327/200) 4096 1153)/2)
    have hp : cPayment 1152 = (82864974964:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1152+point (1327/200) 4096 1153)/2 = (898307:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1152
  · change cPayment 1153 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1153+point (1327/200) 4096 1154)/2)
    have hp : cPayment 1153 = (82865894462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1153+point (1327/200) 4096 1154)/2 = (4492589:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1153
  · change cPayment 1154 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1154+point (1327/200) 4096 1155)/2)
    have hp : cPayment 1154 = (82866752863:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1154+point (1327/200) 4096 1155)/2 = (4493643:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1154
  · change cPayment 1155 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1155+point (1327/200) 4096 1156)/2)
    have hp : cPayment 1155 = (82867550260:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1155+point (1327/200) 4096 1156)/2 = (4494697:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1155
  · change cPayment 1156 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1156+point (1327/200) 4096 1157)/2)
    have hp : cPayment 1156 = (82868286746:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1156+point (1327/200) 4096 1157)/2 = (4495751:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1156
  · change cPayment 1157 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1157+point (1327/200) 4096 1158)/2)
    have hp : cPayment 1157 = (82868962415:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1157+point (1327/200) 4096 1158)/2 = (899361:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1157
  · change cPayment 1158 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1158+point (1327/200) 4096 1159)/2)
    have hp : cPayment 1158 = (82869577361:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1158+point (1327/200) 4096 1159)/2 = (4497859:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1158
  · change cPayment 1159 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1159+point (1327/200) 4096 1160)/2)
    have hp : cPayment 1159 = (82870131674:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1159+point (1327/200) 4096 1160)/2 = (4498913:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1159
  · change cPayment 1160 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1160+point (1327/200) 4096 1161)/2)
    have hp : cPayment 1160 = (82870625450:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1160+point (1327/200) 4096 1161)/2 = (4499967:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1160
  · change cPayment 1161 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1161+point (1327/200) 4096 1162)/2)
    have hp : cPayment 1161 = (82871058780:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1161+point (1327/200) 4096 1162)/2 = (4501021:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1161
  · change cPayment 1162 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1162+point (1327/200) 4096 1163)/2)
    have hp : cPayment 1162 = (82871431756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1162+point (1327/200) 4096 1163)/2 = (180083:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1162
  · change cPayment 1163 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1163+point (1327/200) 4096 1164)/2)
    have hp : cPayment 1163 = (82871744471:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1163+point (1327/200) 4096 1164)/2 = (4503129:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1163
  · change cPayment 1164 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1164+point (1327/200) 4096 1165)/2)
    have hp : cPayment 1164 = (82871997018:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1164+point (1327/200) 4096 1165)/2 = (4504183:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1164
  · change cPayment 1165 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1165+point (1327/200) 4096 1166)/2)
    have hp : cPayment 1165 = (82872189488:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1165+point (1327/200) 4096 1166)/2 = (4505237:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1165
  · change cPayment 1166 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1166+point (1327/200) 4096 1167)/2)
    have hp : cPayment 1166 = (82872321974:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1166+point (1327/200) 4096 1167)/2 = (4506291:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1166
  · change cPayment 1167 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1167+point (1327/200) 4096 1168)/2)
    have hp : cPayment 1167 = (82872394566:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1167+point (1327/200) 4096 1168)/2 = (901469:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1167
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_072
