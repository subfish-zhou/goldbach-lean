import WR2ClassicalCPayments
import WR2ClassicalCPoints091
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_091 (j : Fin 16) : cPayment (16*91+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*91+j.val)+point (1327/200) 4096 (16*91+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1456 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1456+point (1327/200) 4096 1457)/2)
    have hp : cPayment 1456 = (80718979164:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1456+point (1327/200) 4096 1457)/2 = (4811951:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1456
  · change cPayment 1457 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1457+point (1327/200) 4096 1458)/2)
    have hp : cPayment 1457 = (80705046093:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1457+point (1327/200) 4096 1458)/2 = (962601:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1457
  · change cPayment 1458 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1458+point (1327/200) 4096 1459)/2)
    have hp : cPayment 1458 = (80691074763:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1458+point (1327/200) 4096 1459)/2 = (4814059:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1458
  · change cPayment 1459 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1459+point (1327/200) 4096 1460)/2)
    have hp : cPayment 1459 = (80677065236:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1459+point (1327/200) 4096 1460)/2 = (4815113:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1459
  · change cPayment 1460 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1460+point (1327/200) 4096 1461)/2)
    have hp : cPayment 1460 = (80663017569:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1460+point (1327/200) 4096 1461)/2 = (4816167:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1460
  · change cPayment 1461 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1461+point (1327/200) 4096 1462)/2)
    have hp : cPayment 1461 = (80648931824:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1461+point (1327/200) 4096 1462)/2 = (4817221:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1461
  · change cPayment 1462 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1462+point (1327/200) 4096 1463)/2)
    have hp : cPayment 1462 = (80634808058:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1462+point (1327/200) 4096 1463)/2 = (192731:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1462
  · change cPayment 1463 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1463+point (1327/200) 4096 1464)/2)
    have hp : cPayment 1463 = (80620646331:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1463+point (1327/200) 4096 1464)/2 = (4819329:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1463
  · change cPayment 1464 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1464+point (1327/200) 4096 1465)/2)
    have hp : cPayment 1464 = (80606446703:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1464+point (1327/200) 4096 1465)/2 = (4820383:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1464
  · change cPayment 1465 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1465+point (1327/200) 4096 1466)/2)
    have hp : cPayment 1465 = (80592209231:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1465+point (1327/200) 4096 1466)/2 = (4821437:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1465
  · change cPayment 1466 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1466+point (1327/200) 4096 1467)/2)
    have hp : cPayment 1466 = (80577933975:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1466+point (1327/200) 4096 1467)/2 = (4822491:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1466
  · change cPayment 1467 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1467+point (1327/200) 4096 1468)/2)
    have hp : cPayment 1467 = (80563620995:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1467+point (1327/200) 4096 1468)/2 = (964709:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1467
  · change cPayment 1468 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1468+point (1327/200) 4096 1469)/2)
    have hp : cPayment 1468 = (80549270347:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1468+point (1327/200) 4096 1469)/2 = (4824599:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1468
  · change cPayment 1469 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1469+point (1327/200) 4096 1470)/2)
    have hp : cPayment 1469 = (80534882092:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1469+point (1327/200) 4096 1470)/2 = (4825653:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1469
  · change cPayment 1470 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1470+point (1327/200) 4096 1471)/2)
    have hp : cPayment 1470 = (80520456288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1470+point (1327/200) 4096 1471)/2 = (4826707:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1470
  · change cPayment 1471 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1471+point (1327/200) 4096 1472)/2)
    have hp : cPayment 1471 = (80505992993:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1471+point (1327/200) 4096 1472)/2 = (4827761:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1471
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_091
