import WR2ClassicalCPayments
import WR2ClassicalCPoints079
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_079 (j : Fin 16) : cPayment (16*79+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*79+j.val)+point (1327/200) 4096 (16*79+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1264 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1264+point (1327/200) 4096 1265)/2)
    have hp : cPayment 1264 = (82608633602:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1264+point (1327/200) 4096 1265)/2 = (4609583:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1264
  · change cPayment 1265 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1265+point (1327/200) 4096 1266)/2)
    have hp : cPayment 1265 = (82603260325:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1265+point (1327/200) 4096 1266)/2 = (4610637:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1265
  · change cPayment 1266 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1266+point (1327/200) 4096 1267)/2)
    have hp : cPayment 1266 = (82597835589:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1266+point (1327/200) 4096 1267)/2 = (4611691:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1266
  · change cPayment 1267 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1267+point (1327/200) 4096 1268)/2)
    have hp : cPayment 1267 = (82592359473:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1267+point (1327/200) 4096 1268)/2 = (922549:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1267
  · change cPayment 1268 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1268+point (1327/200) 4096 1269)/2)
    have hp : cPayment 1268 = (82586832054:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1268+point (1327/200) 4096 1269)/2 = (4613799:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1268
  · change cPayment 1269 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1269+point (1327/200) 4096 1270)/2)
    have hp : cPayment 1269 = (82581253413:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1269+point (1327/200) 4096 1270)/2 = (4614853:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1269
  · change cPayment 1270 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1270+point (1327/200) 4096 1271)/2)
    have hp : cPayment 1270 = (82575623627:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1270+point (1327/200) 4096 1271)/2 = (4615907:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1270
  · change cPayment 1271 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1271+point (1327/200) 4096 1272)/2)
    have hp : cPayment 1271 = (82569942775:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1271+point (1327/200) 4096 1272)/2 = (4616961:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1271
  · change cPayment 1272 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1272+point (1327/200) 4096 1273)/2)
    have hp : cPayment 1272 = (82564210936:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1272+point (1327/200) 4096 1273)/2 = (923603:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1272
  · change cPayment 1273 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1273+point (1327/200) 4096 1274)/2)
    have hp : cPayment 1273 = (82558428187:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1273+point (1327/200) 4096 1274)/2 = (4619069:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1273
  · change cPayment 1274 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1274+point (1327/200) 4096 1275)/2)
    have hp : cPayment 1274 = (82552594607:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1274+point (1327/200) 4096 1275)/2 = (4620123:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1274
  · change cPayment 1275 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1275+point (1327/200) 4096 1276)/2)
    have hp : cPayment 1275 = (82546710274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1275+point (1327/200) 4096 1276)/2 = (4621177:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1275
  · change cPayment 1276 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1276+point (1327/200) 4096 1277)/2)
    have hp : cPayment 1276 = (82540775265:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1276+point (1327/200) 4096 1277)/2 = (4622231:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1276
  · change cPayment 1277 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1277+point (1327/200) 4096 1278)/2)
    have hp : cPayment 1277 = (82534789659:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1277+point (1327/200) 4096 1278)/2 = (924657:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1277
  · change cPayment 1278 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1278+point (1327/200) 4096 1279)/2)
    have hp : cPayment 1278 = (82528753532:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1278+point (1327/200) 4096 1279)/2 = (4624339:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1278
  · change cPayment 1279 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1279+point (1327/200) 4096 1280)/2)
    have hp : cPayment 1279 = (82522666964:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1279+point (1327/200) 4096 1280)/2 = (4625393:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1279
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_079
