import WR2ClassicalCPayments
import WR2ClassicalCPoints089
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_089 (j : Fin 16) : cPayment (16*89+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*89+j.val)+point (1327/200) 4096 (16*89+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1424 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1424+point (1327/200) 4096 1425)/2)
    have hp : cPayment 1424 = (81144276837:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1424+point (1327/200) 4096 1425)/2 = (4778223:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1424
  · change cPayment 1425 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1425+point (1327/200) 4096 1426)/2)
    have hp : cPayment 1425 = (81131599947:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1425+point (1327/200) 4096 1426)/2 = (4779277:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1425
  · change cPayment 1426 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1426+point (1327/200) 4096 1427)/2)
    have hp : cPayment 1426 = (81118882849:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1426+point (1327/200) 4096 1427)/2 = (4780331:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1426
  · change cPayment 1427 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1427+point (1327/200) 4096 1428)/2)
    have hp : cPayment 1427 = (81106125606:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1427+point (1327/200) 4096 1428)/2 = (956277:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1427
  · change cPayment 1428 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1428+point (1327/200) 4096 1429)/2)
    have hp : cPayment 1428 = (81093328280:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1428+point (1327/200) 4096 1429)/2 = (4782439:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1428
  · change cPayment 1429 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1429+point (1327/200) 4096 1430)/2)
    have hp : cPayment 1429 = (81080490932:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1429+point (1327/200) 4096 1430)/2 = (4783493:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1429
  · change cPayment 1430 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1430+point (1327/200) 4096 1431)/2)
    have hp : cPayment 1430 = (81067613625:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1430+point (1327/200) 4096 1431)/2 = (4784547:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1430
  · change cPayment 1431 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1431+point (1327/200) 4096 1432)/2)
    have hp : cPayment 1431 = (81054696421:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1431+point (1327/200) 4096 1432)/2 = (4785601:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1431
  · change cPayment 1432 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1432+point (1327/200) 4096 1433)/2)
    have hp : cPayment 1432 = (81041739381:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1432+point (1327/200) 4096 1433)/2 = (957331:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1432
  · change cPayment 1433 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1433+point (1327/200) 4096 1434)/2)
    have hp : cPayment 1433 = (81028742568:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1433+point (1327/200) 4096 1434)/2 = (4787709:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1433
  · change cPayment 1434 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1434+point (1327/200) 4096 1435)/2)
    have hp : cPayment 1434 = (81015706044:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1434+point (1327/200) 4096 1435)/2 = (4788763:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1434
  · change cPayment 1435 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1435+point (1327/200) 4096 1436)/2)
    have hp : cPayment 1435 = (81002629869:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1435+point (1327/200) 4096 1436)/2 = (4789817:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1435
  · change cPayment 1436 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1436+point (1327/200) 4096 1437)/2)
    have hp : cPayment 1436 = (80989514105:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1436+point (1327/200) 4096 1437)/2 = (4790871:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1436
  · change cPayment 1437 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1437+point (1327/200) 4096 1438)/2)
    have hp : cPayment 1437 = (80976358814:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1437+point (1327/200) 4096 1438)/2 = (191677:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1437
  · change cPayment 1438 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1438+point (1327/200) 4096 1439)/2)
    have hp : cPayment 1438 = (80963164057:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1438+point (1327/200) 4096 1439)/2 = (4792979:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1438
  · change cPayment 1439 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1439+point (1327/200) 4096 1440)/2)
    have hp : cPayment 1439 = (80949929896:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1439+point (1327/200) 4096 1440)/2 = (4794033:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1439
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_089
