import WR2ClassicalCPayments
import WR2ClassicalCPoints088
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_088 (j : Fin 16) : cPayment (16*88+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*88+j.val)+point (1327/200) 4096 (16*88+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1408 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1408+point (1327/200) 4096 1409)/2)
    have hp : cPayment 1408 = (81341587579:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1408+point (1327/200) 4096 1409)/2 = (4761359:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1408
  · change cPayment 1409 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1409+point (1327/200) 4096 1410)/2)
    have hp : cPayment 1409 = (81329562567:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1409+point (1327/200) 4096 1410)/2 = (4762413:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1409
  · change cPayment 1410 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1410+point (1327/200) 4096 1411)/2)
    have hp : cPayment 1410 = (81317496338:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1410+point (1327/200) 4096 1411)/2 = (4763467:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1410
  · change cPayment 1411 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1411+point (1327/200) 4096 1412)/2)
    have hp : cPayment 1411 = (81305388956:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1411+point (1327/200) 4096 1412)/2 = (4764521:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1411
  · change cPayment 1412 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1412+point (1327/200) 4096 1413)/2)
    have hp : cPayment 1412 = (81293240482:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1412+point (1327/200) 4096 1413)/2 = (190623:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1412
  · change cPayment 1413 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1413+point (1327/200) 4096 1414)/2)
    have hp : cPayment 1413 = (81281050983:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1413+point (1327/200) 4096 1414)/2 = (4766629:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1413
  · change cPayment 1414 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1414+point (1327/200) 4096 1415)/2)
    have hp : cPayment 1414 = (81268820520:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1414+point (1327/200) 4096 1415)/2 = (4767683:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1414
  · change cPayment 1415 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1415+point (1327/200) 4096 1416)/2)
    have hp : cPayment 1415 = (81256549158:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1415+point (1327/200) 4096 1416)/2 = (4768737:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1415
  · change cPayment 1416 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1416+point (1327/200) 4096 1417)/2)
    have hp : cPayment 1416 = (81244236960:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1416+point (1327/200) 4096 1417)/2 = (4769791:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1416
  · change cPayment 1417 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1417+point (1327/200) 4096 1418)/2)
    have hp : cPayment 1417 = (81231883988:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1417+point (1327/200) 4096 1418)/2 = (954169:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1417
  · change cPayment 1418 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1418+point (1327/200) 4096 1419)/2)
    have hp : cPayment 1418 = (81219490307:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1418+point (1327/200) 4096 1419)/2 = (4771899:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1418
  · change cPayment 1419 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1419+point (1327/200) 4096 1420)/2)
    have hp : cPayment 1419 = (81207055979:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1419+point (1327/200) 4096 1420)/2 = (4772953:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1419
  · change cPayment 1420 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1420+point (1327/200) 4096 1421)/2)
    have hp : cPayment 1420 = (81194581067:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1420+point (1327/200) 4096 1421)/2 = (4774007:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1420
  · change cPayment 1421 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1421+point (1327/200) 4096 1422)/2)
    have hp : cPayment 1421 = (81182065634:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1421+point (1327/200) 4096 1422)/2 = (4775061:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1421
  · change cPayment 1422 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1422+point (1327/200) 4096 1423)/2)
    have hp : cPayment 1422 = (81169509743:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1422+point (1327/200) 4096 1423)/2 = (955223:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1422
  · change cPayment 1423 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1423+point (1327/200) 4096 1424)/2)
    have hp : cPayment 1423 = (81156913456:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1423+point (1327/200) 4096 1424)/2 = (4777169:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1423
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_088
