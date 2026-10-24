import WR2ClassicalCPayments
import WR2ClassicalCPoints074
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_074 (j : Fin 16) : cPayment (16*74+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*74+j.val)+point (1327/200) 4096 (16*74+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1184 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1184+point (1327/200) 4096 1185)/2)
    have hp : cPayment 1184 = (82864553311:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1184+point (1327/200) 4096 1185)/2 = (4525263:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1184
  · change cPayment 1185 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1185+point (1327/200) 4096 1186)/2)
    have hp : cPayment 1185 = (82863563371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1185+point (1327/200) 4096 1186)/2 = (4526317:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1185
  · change cPayment 1186 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1186+point (1327/200) 4096 1187)/2)
    have hp : cPayment 1186 = (82862515257:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1186+point (1327/200) 4096 1187)/2 = (4527371:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1186
  · change cPayment 1187 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1187+point (1327/200) 4096 1188)/2)
    have hp : cPayment 1187 = (82861409057:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1187+point (1327/200) 4096 1188)/2 = (181137:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1187
  · change cPayment 1188 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1188+point (1327/200) 4096 1189)/2)
    have hp : cPayment 1188 = (82860244860:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1188+point (1327/200) 4096 1189)/2 = (4529479:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1188
  · change cPayment 1189 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1189+point (1327/200) 4096 1190)/2)
    have hp : cPayment 1189 = (82859022754:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1189+point (1327/200) 4096 1190)/2 = (4530533:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1189
  · change cPayment 1190 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1190+point (1327/200) 4096 1191)/2)
    have hp : cPayment 1190 = (82857742829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1190+point (1327/200) 4096 1191)/2 = (4531587:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1190
  · change cPayment 1191 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1191+point (1327/200) 4096 1192)/2)
    have hp : cPayment 1191 = (82856405174:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1191+point (1327/200) 4096 1192)/2 = (4532641:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1191
  · change cPayment 1192 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1192+point (1327/200) 4096 1193)/2)
    have hp : cPayment 1192 = (82855009875:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1192+point (1327/200) 4096 1193)/2 = (906739:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1192
  · change cPayment 1193 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1193+point (1327/200) 4096 1194)/2)
    have hp : cPayment 1193 = (82853557022:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1193+point (1327/200) 4096 1194)/2 = (4534749:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1193
  · change cPayment 1194 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1194+point (1327/200) 4096 1195)/2)
    have hp : cPayment 1194 = (82852046703:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1194+point (1327/200) 4096 1195)/2 = (4535803:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1194
  · change cPayment 1195 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1195+point (1327/200) 4096 1196)/2)
    have hp : cPayment 1195 = (82850479005:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1195+point (1327/200) 4096 1196)/2 = (4536857:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1195
  · change cPayment 1196 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1196+point (1327/200) 4096 1197)/2)
    have hp : cPayment 1196 = (82848854017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1196+point (1327/200) 4096 1197)/2 = (4537911:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1196
  · change cPayment 1197 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1197+point (1327/200) 4096 1198)/2)
    have hp : cPayment 1197 = (82847171827:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1197+point (1327/200) 4096 1198)/2 = (907793:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1197
  · change cPayment 1198 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1198+point (1327/200) 4096 1199)/2)
    have hp : cPayment 1198 = (82845432521:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1198+point (1327/200) 4096 1199)/2 = (4540019:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1198
  · change cPayment 1199 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1199+point (1327/200) 4096 1200)/2)
    have hp : cPayment 1199 = (82843636187:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1199+point (1327/200) 4096 1200)/2 = (4541073:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1199
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_074
