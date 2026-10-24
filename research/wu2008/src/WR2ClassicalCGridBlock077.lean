import WR2ClassicalCPayments
import WR2ClassicalCPoints077
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_077 (j : Fin 16) : cPayment (16*77+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*77+j.val)+point (1327/200) 4096 (16*77+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1232 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1232+point (1327/200) 4096 1233)/2)
    have hp : cPayment 1232 = (82752929240:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1232+point (1327/200) 4096 1233)/2 = (915171:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1232
  · change cPayment 1233 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1233+point (1327/200) 4096 1234)/2)
    have hp : cPayment 1233 = (82749245061:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1233+point (1327/200) 4096 1234)/2 = (4576909:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1233
  · change cPayment 1234 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1234+point (1327/200) 4096 1235)/2)
    have hp : cPayment 1234 = (82745506834:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1234+point (1327/200) 4096 1235)/2 = (4577963:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1234
  · change cPayment 1235 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1235+point (1327/200) 4096 1236)/2)
    have hp : cPayment 1235 = (82741714640:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1235+point (1327/200) 4096 1236)/2 = (4579017:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1235
  · change cPayment 1236 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1236+point (1327/200) 4096 1237)/2)
    have hp : cPayment 1236 = (82737868564:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1236+point (1327/200) 4096 1237)/2 = (4580071:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1236
  · change cPayment 1237 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1237+point (1327/200) 4096 1238)/2)
    have hp : cPayment 1237 = (82733968686:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1237+point (1327/200) 4096 1238)/2 = (183245:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1237
  · change cPayment 1238 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1238+point (1327/200) 4096 1239)/2)
    have hp : cPayment 1238 = (82730015090:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1238+point (1327/200) 4096 1239)/2 = (4582179:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1238
  · change cPayment 1239 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1239+point (1327/200) 4096 1240)/2)
    have hp : cPayment 1239 = (82726007858:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1239+point (1327/200) 4096 1240)/2 = (4583233:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1239
  · change cPayment 1240 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1240+point (1327/200) 4096 1241)/2)
    have hp : cPayment 1240 = (82721947071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1240+point (1327/200) 4096 1241)/2 = (4584287:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1240
  · change cPayment 1241 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1241+point (1327/200) 4096 1242)/2)
    have hp : cPayment 1241 = (82717832814:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1241+point (1327/200) 4096 1242)/2 = (4585341:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1241
  · change cPayment 1242 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1242+point (1327/200) 4096 1243)/2)
    have hp : cPayment 1242 = (82713665166:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1242+point (1327/200) 4096 1243)/2 = (917279:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1242
  · change cPayment 1243 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1243+point (1327/200) 4096 1244)/2)
    have hp : cPayment 1243 = (82709444210:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1243+point (1327/200) 4096 1244)/2 = (4587449:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1243
  · change cPayment 1244 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1244+point (1327/200) 4096 1245)/2)
    have hp : cPayment 1244 = (82705170028:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1244+point (1327/200) 4096 1245)/2 = (4588503:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1244
  · change cPayment 1245 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1245+point (1327/200) 4096 1246)/2)
    have hp : cPayment 1245 = (82700842701:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1245+point (1327/200) 4096 1246)/2 = (4589557:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1245
  · change cPayment 1246 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1246+point (1327/200) 4096 1247)/2)
    have hp : cPayment 1246 = (82696462311:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1246+point (1327/200) 4096 1247)/2 = (4590611:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1246
  · change cPayment 1247 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1247+point (1327/200) 4096 1248)/2)
    have hp : cPayment 1247 = (82692028938:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1247+point (1327/200) 4096 1248)/2 = (918333:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1247
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_077
