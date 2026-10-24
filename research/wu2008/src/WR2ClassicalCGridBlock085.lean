import WR2ClassicalCPayments
import WR2ClassicalCPoints085
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_085 (j : Fin 16) : cPayment (16*85+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*85+j.val)+point (1327/200) 4096 (16*85+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1360 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1360+point (1327/200) 4096 1361)/2)
    have hp : cPayment 1360 = (81869041910:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1360+point (1327/200) 4096 1361)/2 = (4710767:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1360
  · change cPayment 1361 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1361+point (1327/200) 4096 1362)/2)
    have hp : cPayment 1361 = (81859072244:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1361+point (1327/200) 4096 1362)/2 = (4711821:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1361
  · change cPayment 1362 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1362+point (1327/200) 4096 1363)/2)
    have hp : cPayment 1362 = (81849058185:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1362+point (1327/200) 4096 1363)/2 = (188515:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1362
  · change cPayment 1363 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1363+point (1327/200) 4096 1364)/2)
    have hp : cPayment 1363 = (81838999801:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1363+point (1327/200) 4096 1364)/2 = (4713929:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1363
  · change cPayment 1364 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1364+point (1327/200) 4096 1365)/2)
    have hp : cPayment 1364 = (81828897162:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1364+point (1327/200) 4096 1365)/2 = (4714983:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1364
  · change cPayment 1365 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1365+point (1327/200) 4096 1366)/2)
    have hp : cPayment 1365 = (81818750335:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1365+point (1327/200) 4096 1366)/2 = (4716037:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1365
  · change cPayment 1366 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1366+point (1327/200) 4096 1367)/2)
    have hp : cPayment 1366 = (81808559388:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1366+point (1327/200) 4096 1367)/2 = (4717091:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1366
  · change cPayment 1367 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1367+point (1327/200) 4096 1368)/2)
    have hp : cPayment 1367 = (81798324390:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1367+point (1327/200) 4096 1368)/2 = (943629:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1367
  · change cPayment 1368 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1368+point (1327/200) 4096 1369)/2)
    have hp : cPayment 1368 = (81788045408:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1368+point (1327/200) 4096 1369)/2 = (4719199:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1368
  · change cPayment 1369 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1369+point (1327/200) 4096 1370)/2)
    have hp : cPayment 1369 = (81777722511:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1369+point (1327/200) 4096 1370)/2 = (4720253:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1369
  · change cPayment 1370 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1370+point (1327/200) 4096 1371)/2)
    have hp : cPayment 1370 = (81767355766:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1370+point (1327/200) 4096 1371)/2 = (4721307:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1370
  · change cPayment 1371 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1371+point (1327/200) 4096 1372)/2)
    have hp : cPayment 1371 = (81756945240:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1371+point (1327/200) 4096 1372)/2 = (4722361:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1371
  · change cPayment 1372 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1372+point (1327/200) 4096 1373)/2)
    have hp : cPayment 1372 = (81746491002:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1372+point (1327/200) 4096 1373)/2 = (944683:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1372
  · change cPayment 1373 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1373+point (1327/200) 4096 1374)/2)
    have hp : cPayment 1373 = (81735993118:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1373+point (1327/200) 4096 1374)/2 = (4724469:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1373
  · change cPayment 1374 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1374+point (1327/200) 4096 1375)/2)
    have hp : cPayment 1374 = (81725451657:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1374+point (1327/200) 4096 1375)/2 = (4725523:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1374
  · change cPayment 1375 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1375+point (1327/200) 4096 1376)/2)
    have hp : cPayment 1375 = (81714866685:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1375+point (1327/200) 4096 1376)/2 = (4726577:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1375
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_085
