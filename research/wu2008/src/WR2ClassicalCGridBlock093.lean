import WR2ClassicalCPayments
import WR2ClassicalCPoints093
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_093 (j : Fin 16) : cPayment (16*93+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*93+j.val)+point (1327/200) 4096 (16*93+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1488 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1488+point (1327/200) 4096 1489)/2)
    have hp : cPayment 1488 = (80254437135:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1488+point (1327/200) 4096 1489)/2 = (4845679:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1488
  · change cPayment 1489 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1489+point (1327/200) 4096 1490)/2)
    have hp : cPayment 1489 = (80239308908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1489+point (1327/200) 4096 1490)/2 = (4846733:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1489
  · change cPayment 1490 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1490+point (1327/200) 4096 1491)/2)
    have hp : cPayment 1490 = (80224144286:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1490+point (1327/200) 4096 1491)/2 = (4847787:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1490
  · change cPayment 1491 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1491+point (1327/200) 4096 1492)/2)
    have hp : cPayment 1491 = (80208943325:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1491+point (1327/200) 4096 1492)/2 = (4848841:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1491
  · change cPayment 1492 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1492+point (1327/200) 4096 1493)/2)
    have hp : cPayment 1492 = (80193706082:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1492+point (1327/200) 4096 1493)/2 = (969979:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1492
  · change cPayment 1493 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1493+point (1327/200) 4096 1494)/2)
    have hp : cPayment 1493 = (80178432613:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1493+point (1327/200) 4096 1494)/2 = (4850949:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1493
  · change cPayment 1494 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1494+point (1327/200) 4096 1495)/2)
    have hp : cPayment 1494 = (80163122975:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1494+point (1327/200) 4096 1495)/2 = (4852003:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1494
  · change cPayment 1495 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1495+point (1327/200) 4096 1496)/2)
    have hp : cPayment 1495 = (80147777225:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1495+point (1327/200) 4096 1496)/2 = (4853057:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1495
  · change cPayment 1496 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1496+point (1327/200) 4096 1497)/2)
    have hp : cPayment 1496 = (80132395419:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1496+point (1327/200) 4096 1497)/2 = (4854111:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1496
  · change cPayment 1497 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1497+point (1327/200) 4096 1498)/2)
    have hp : cPayment 1497 = (80116977613:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1497+point (1327/200) 4096 1498)/2 = (971033:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1497
  · change cPayment 1498 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1498+point (1327/200) 4096 1499)/2)
    have hp : cPayment 1498 = (80101523863:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1498+point (1327/200) 4096 1499)/2 = (4856219:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1498
  · change cPayment 1499 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1499+point (1327/200) 4096 1500)/2)
    have hp : cPayment 1499 = (80086034226:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1499+point (1327/200) 4096 1500)/2 = (4857273:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1499
  · change cPayment 1500 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1500+point (1327/200) 4096 1501)/2)
    have hp : cPayment 1500 = (80070508758:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1500+point (1327/200) 4096 1501)/2 = (4858327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1500
  · change cPayment 1501 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1501+point (1327/200) 4096 1502)/2)
    have hp : cPayment 1501 = (80054947514:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1501+point (1327/200) 4096 1502)/2 = (4859381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1501
  · change cPayment 1502 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1502+point (1327/200) 4096 1503)/2)
    have hp : cPayment 1502 = (80039350551:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1502+point (1327/200) 4096 1503)/2 = (972087:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1502
  · change cPayment 1503 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1503+point (1327/200) 4096 1504)/2)
    have hp : cPayment 1503 = (80023717925:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1503+point (1327/200) 4096 1504)/2 = (4861489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1503
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_093
