import WR2ClassicalCPayments
import WR2ClassicalCPoints092
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_092 (j : Fin 16) : cPayment (16*92+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*92+j.val)+point (1327/200) 4096 (16*92+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1472 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1472+point (1327/200) 4096 1473)/2)
    have hp : cPayment 1472 = (80491492265:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1472+point (1327/200) 4096 1473)/2 = (965763:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1472
  · change cPayment 1473 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1473+point (1327/200) 4096 1474)/2)
    have hp : cPayment 1473 = (80476954163:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1473+point (1327/200) 4096 1474)/2 = (4829869:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1473
  · change cPayment 1474 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1474+point (1327/200) 4096 1475)/2)
    have hp : cPayment 1474 = (80462378746:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1474+point (1327/200) 4096 1475)/2 = (4830923:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1474
  · change cPayment 1475 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1475+point (1327/200) 4096 1476)/2)
    have hp : cPayment 1475 = (80447766070:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1475+point (1327/200) 4096 1476)/2 = (4831977:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1475
  · change cPayment 1476 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1476+point (1327/200) 4096 1477)/2)
    have hp : cPayment 1476 = (80433116195:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1476+point (1327/200) 4096 1477)/2 = (4833031:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1476
  · change cPayment 1477 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1477+point (1327/200) 4096 1478)/2)
    have hp : cPayment 1477 = (80418429178:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1477+point (1327/200) 4096 1478)/2 = (966817:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1477
  · change cPayment 1478 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1478+point (1327/200) 4096 1479)/2)
    have hp : cPayment 1478 = (80403705078:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1478+point (1327/200) 4096 1479)/2 = (4835139:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1478
  · change cPayment 1479 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1479+point (1327/200) 4096 1480)/2)
    have hp : cPayment 1479 = (80388943951:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1479+point (1327/200) 4096 1480)/2 = (4836193:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1479
  · change cPayment 1480 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1480+point (1327/200) 4096 1481)/2)
    have hp : cPayment 1480 = (80374145856:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1480+point (1327/200) 4096 1481)/2 = (4837247:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1480
  · change cPayment 1481 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1481+point (1327/200) 4096 1482)/2)
    have hp : cPayment 1481 = (80359310850:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1481+point (1327/200) 4096 1482)/2 = (4838301:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1481
  · change cPayment 1482 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1482+point (1327/200) 4096 1483)/2)
    have hp : cPayment 1482 = (80344438991:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1482+point (1327/200) 4096 1483)/2 = (967871:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1482
  · change cPayment 1483 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1483+point (1327/200) 4096 1484)/2)
    have hp : cPayment 1483 = (80329530337:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1483+point (1327/200) 4096 1484)/2 = (4840409:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1483
  · change cPayment 1484 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1484+point (1327/200) 4096 1485)/2)
    have hp : cPayment 1484 = (80314584944:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1484+point (1327/200) 4096 1485)/2 = (4841463:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1484
  · change cPayment 1485 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1485+point (1327/200) 4096 1486)/2)
    have hp : cPayment 1485 = (80299602870:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1485+point (1327/200) 4096 1486)/2 = (4842517:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1485
  · change cPayment 1486 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1486+point (1327/200) 4096 1487)/2)
    have hp : cPayment 1486 = (80284584173:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1486+point (1327/200) 4096 1487)/2 = (4843571:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1486
  · change cPayment 1487 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1487+point (1327/200) 4096 1488)/2)
    have hp : cPayment 1487 = (80269528908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1487+point (1327/200) 4096 1488)/2 = (193785:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1487
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_092
