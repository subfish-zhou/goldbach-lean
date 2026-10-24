import WR2ClassicalCPayments
import WR2ClassicalCPoints086
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_086 (j : Fin 16) : cPayment (16*86+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*86+j.val)+point (1327/200) 4096 (16*86+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1376 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1376+point (1327/200) 4096 1377)/2)
    have hp : cPayment 1376 = (81704238269:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1376+point (1327/200) 4096 1377)/2 = (4727631:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1376
  · change cPayment 1377 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1377+point (1327/200) 4096 1378)/2)
    have hp : cPayment 1377 = (81693566477:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1377+point (1327/200) 4096 1378)/2 = (945737:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1377
  · change cPayment 1378 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1378+point (1327/200) 4096 1379)/2)
    have hp : cPayment 1378 = (81682851376:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1378+point (1327/200) 4096 1379)/2 = (4729739:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1378
  · change cPayment 1379 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1379+point (1327/200) 4096 1380)/2)
    have hp : cPayment 1379 = (81672093032:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1379+point (1327/200) 4096 1380)/2 = (4730793:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1379
  · change cPayment 1380 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1380+point (1327/200) 4096 1381)/2)
    have hp : cPayment 1380 = (81661291512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1380+point (1327/200) 4096 1381)/2 = (4731847:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1380
  · change cPayment 1381 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1381+point (1327/200) 4096 1382)/2)
    have hp : cPayment 1381 = (81650446883:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1381+point (1327/200) 4096 1382)/2 = (4732901:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1381
  · change cPayment 1382 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1382+point (1327/200) 4096 1383)/2)
    have hp : cPayment 1382 = (81639559211:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1382+point (1327/200) 4096 1383)/2 = (946791:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1382
  · change cPayment 1383 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1383+point (1327/200) 4096 1384)/2)
    have hp : cPayment 1383 = (81628628563:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1383+point (1327/200) 4096 1384)/2 = (4735009:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1383
  · change cPayment 1384 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1384+point (1327/200) 4096 1385)/2)
    have hp : cPayment 1384 = (81617655006:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1384+point (1327/200) 4096 1385)/2 = (4736063:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1384
  · change cPayment 1385 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1385+point (1327/200) 4096 1386)/2)
    have hp : cPayment 1385 = (81606638605:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1385+point (1327/200) 4096 1386)/2 = (4737117:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1385
  · change cPayment 1386 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1386+point (1327/200) 4096 1387)/2)
    have hp : cPayment 1386 = (81595579426:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1386+point (1327/200) 4096 1387)/2 = (4738171:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1386
  · change cPayment 1387 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1387+point (1327/200) 4096 1388)/2)
    have hp : cPayment 1387 = (81584477537:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1387+point (1327/200) 4096 1388)/2 = (189569:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1387
  · change cPayment 1388 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1388+point (1327/200) 4096 1389)/2)
    have hp : cPayment 1388 = (81573333002:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1388+point (1327/200) 4096 1389)/2 = (4740279:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1388
  · change cPayment 1389 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1389+point (1327/200) 4096 1390)/2)
    have hp : cPayment 1389 = (81562145888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1389+point (1327/200) 4096 1390)/2 = (4741333:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1389
  · change cPayment 1390 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1390+point (1327/200) 4096 1391)/2)
    have hp : cPayment 1390 = (81550916260:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1390+point (1327/200) 4096 1391)/2 = (4742387:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1390
  · change cPayment 1391 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1391+point (1327/200) 4096 1392)/2)
    have hp : cPayment 1391 = (81539644185:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1391+point (1327/200) 4096 1392)/2 = (4743441:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1391
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_086
