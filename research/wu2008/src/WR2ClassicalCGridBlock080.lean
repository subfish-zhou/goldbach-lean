import WR2ClassicalCPayments
import WR2ClassicalCPoints080
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_080 (j : Fin 16) : cPayment (16*80+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*80+j.val)+point (1327/200) 4096 (16*80+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1280 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1280+point (1327/200) 4096 1281)/2)
    have hp : cPayment 1280 = (82516530030:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1280+point (1327/200) 4096 1281)/2 = (4626447:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1280
  · change cPayment 1281 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1281+point (1327/200) 4096 1282)/2)
    have hp : cPayment 1281 = (82510342808:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1281+point (1327/200) 4096 1282)/2 = (4627501:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1281
  · change cPayment 1282 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1282+point (1327/200) 4096 1283)/2)
    have hp : cPayment 1282 = (82504105376:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1282+point (1327/200) 4096 1283)/2 = (925711:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1282
  · change cPayment 1283 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1283+point (1327/200) 4096 1284)/2)
    have hp : cPayment 1283 = (82497817810:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1283+point (1327/200) 4096 1284)/2 = (4629609:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1283
  · change cPayment 1284 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1284+point (1327/200) 4096 1285)/2)
    have hp : cPayment 1284 = (82491480188:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1284+point (1327/200) 4096 1285)/2 = (4630663:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1284
  · change cPayment 1285 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1285+point (1327/200) 4096 1286)/2)
    have hp : cPayment 1285 = (82485092586:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1285+point (1327/200) 4096 1286)/2 = (4631717:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1285
  · change cPayment 1286 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1286+point (1327/200) 4096 1287)/2)
    have hp : cPayment 1286 = (82478655081:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1286+point (1327/200) 4096 1287)/2 = (4632771:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1286
  · change cPayment 1287 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1287+point (1327/200) 4096 1288)/2)
    have hp : cPayment 1287 = (82472167750:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1287+point (1327/200) 4096 1288)/2 = (185353:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1287
  · change cPayment 1288 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1288+point (1327/200) 4096 1289)/2)
    have hp : cPayment 1288 = (82465630669:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1288+point (1327/200) 4096 1289)/2 = (4634879:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1288
  · change cPayment 1289 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1289+point (1327/200) 4096 1290)/2)
    have hp : cPayment 1289 = (82459043915:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1289+point (1327/200) 4096 1290)/2 = (4635933:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1289
  · change cPayment 1290 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1290+point (1327/200) 4096 1291)/2)
    have hp : cPayment 1290 = (82452407563:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1290+point (1327/200) 4096 1291)/2 = (4636987:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1290
  · change cPayment 1291 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1291+point (1327/200) 4096 1292)/2)
    have hp : cPayment 1291 = (82445721691:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1291+point (1327/200) 4096 1292)/2 = (4638041:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1291
  · change cPayment 1292 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1292+point (1327/200) 4096 1293)/2)
    have hp : cPayment 1292 = (82438986373:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1292+point (1327/200) 4096 1293)/2 = (927819:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1292
  · change cPayment 1293 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1293+point (1327/200) 4096 1294)/2)
    have hp : cPayment 1293 = (82432201686:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1293+point (1327/200) 4096 1294)/2 = (4640149:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1293
  · change cPayment 1294 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1294+point (1327/200) 4096 1295)/2)
    have hp : cPayment 1294 = (82425367706:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1294+point (1327/200) 4096 1295)/2 = (4641203:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1294
  · change cPayment 1295 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1295+point (1327/200) 4096 1296)/2)
    have hp : cPayment 1295 = (82418484509:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1295+point (1327/200) 4096 1296)/2 = (4642257:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1295
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_080
