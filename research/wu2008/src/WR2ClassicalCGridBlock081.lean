import WR2ClassicalCPayments
import WR2ClassicalCPoints081
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_081 (j : Fin 16) : cPayment (16*81+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*81+j.val)+point (1327/200) 4096 (16*81+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1296 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1296+point (1327/200) 4096 1297)/2)
    have hp : cPayment 1296 = (82411552169:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1296+point (1327/200) 4096 1297)/2 = (4643311:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1296
  · change cPayment 1297 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1297+point (1327/200) 4096 1298)/2)
    have hp : cPayment 1297 = (82404570764:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1297+point (1327/200) 4096 1298)/2 = (928873:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1297
  · change cPayment 1298 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1298+point (1327/200) 4096 1299)/2)
    have hp : cPayment 1298 = (82397540367:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1298+point (1327/200) 4096 1299)/2 = (4645419:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1298
  · change cPayment 1299 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1299+point (1327/200) 4096 1300)/2)
    have hp : cPayment 1299 = (82390461054:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1299+point (1327/200) 4096 1300)/2 = (4646473:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1299
  · change cPayment 1300 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1300+point (1327/200) 4096 1301)/2)
    have hp : cPayment 1300 = (82383332900:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1300+point (1327/200) 4096 1301)/2 = (4647527:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1300
  · change cPayment 1301 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1301+point (1327/200) 4096 1302)/2)
    have hp : cPayment 1301 = (82376155981:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1301+point (1327/200) 4096 1302)/2 = (4648581:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1301
  · change cPayment 1302 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1302+point (1327/200) 4096 1303)/2)
    have hp : cPayment 1302 = (82368930371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1302+point (1327/200) 4096 1303)/2 = (929927:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1302
  · change cPayment 1303 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1303+point (1327/200) 4096 1304)/2)
    have hp : cPayment 1303 = (82361656146:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1303+point (1327/200) 4096 1304)/2 = (4650689:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1303
  · change cPayment 1304 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1304+point (1327/200) 4096 1305)/2)
    have hp : cPayment 1304 = (82354333379:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1304+point (1327/200) 4096 1305)/2 = (4651743:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1304
  · change cPayment 1305 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1305+point (1327/200) 4096 1306)/2)
    have hp : cPayment 1305 = (82346962145:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1305+point (1327/200) 4096 1306)/2 = (4652797:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1305
  · change cPayment 1306 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1306+point (1327/200) 4096 1307)/2)
    have hp : cPayment 1306 = (82339542519:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1306+point (1327/200) 4096 1307)/2 = (4653851:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1306
  · change cPayment 1307 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1307+point (1327/200) 4096 1308)/2)
    have hp : cPayment 1307 = (82332074575:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1307+point (1327/200) 4096 1308)/2 = (930981:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1307
  · change cPayment 1308 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1308+point (1327/200) 4096 1309)/2)
    have hp : cPayment 1308 = (82324558388:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1308+point (1327/200) 4096 1309)/2 = (4655959:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1308
  · change cPayment 1309 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1309+point (1327/200) 4096 1310)/2)
    have hp : cPayment 1309 = (82316994032:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1309+point (1327/200) 4096 1310)/2 = (4657013:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1309
  · change cPayment 1310 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1310+point (1327/200) 4096 1311)/2)
    have hp : cPayment 1310 = (82309381580:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1310+point (1327/200) 4096 1311)/2 = (4658067:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1310
  · change cPayment 1311 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1311+point (1327/200) 4096 1312)/2)
    have hp : cPayment 1311 = (82301721106:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1311+point (1327/200) 4096 1312)/2 = (4659121:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1311
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_081
