import WR2ClassicalCPayments
import WR2ClassicalCPoints095
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_095 (j : Fin 16) : cPayment (16*95+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*95+j.val)+point (1327/200) 4096 (16*95+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1520 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1520+point (1327/200) 4096 1521)/2)
    have hp : cPayment 1520 = (79752560465:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1520+point (1327/200) 4096 1521)/2 = (4879407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1520
  · change cPayment 1521 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1521+point (1327/200) 4096 1522)/2)
    have hp : cPayment 1521 = (79736295351:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1521+point (1327/200) 4096 1522)/2 = (4880461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1521
  · change cPayment 1522 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1522+point (1327/200) 4096 1523)/2)
    have hp : cPayment 1522 = (79719995619:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1522+point (1327/200) 4096 1523)/2 = (976303:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1522
  · change cPayment 1523 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1523+point (1327/200) 4096 1524)/2)
    have hp : cPayment 1523 = (79703661324:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1523+point (1327/200) 4096 1524)/2 = (4882569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1523
  · change cPayment 1524 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1524+point (1327/200) 4096 1525)/2)
    have hp : cPayment 1524 = (79687292519:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1524+point (1327/200) 4096 1525)/2 = (4883623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1524
  · change cPayment 1525 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1525+point (1327/200) 4096 1526)/2)
    have hp : cPayment 1525 = (79670889259:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1525+point (1327/200) 4096 1526)/2 = (4884677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1525
  · change cPayment 1526 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1526+point (1327/200) 4096 1527)/2)
    have hp : cPayment 1526 = (79654451597:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1526+point (1327/200) 4096 1527)/2 = (4885731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1526
  · change cPayment 1527 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1527+point (1327/200) 4096 1528)/2)
    have hp : cPayment 1527 = (79637979589:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1527+point (1327/200) 4096 1528)/2 = (977357:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1527
  · change cPayment 1528 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1528+point (1327/200) 4096 1529)/2)
    have hp : cPayment 1528 = (79621473286:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1528+point (1327/200) 4096 1529)/2 = (4887839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1528
  · change cPayment 1529 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1529+point (1327/200) 4096 1530)/2)
    have hp : cPayment 1529 = (79604932744:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1529+point (1327/200) 4096 1530)/2 = (4888893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1529
  · change cPayment 1530 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1530+point (1327/200) 4096 1531)/2)
    have hp : cPayment 1530 = (79588358017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1530+point (1327/200) 4096 1531)/2 = (4889947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1530
  · change cPayment 1531 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1531+point (1327/200) 4096 1532)/2)
    have hp : cPayment 1531 = (79571749156:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1531+point (1327/200) 4096 1532)/2 = (4891001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1531
  · change cPayment 1532 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1532+point (1327/200) 4096 1533)/2)
    have hp : cPayment 1532 = (79555106217:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1532+point (1327/200) 4096 1533)/2 = (978411:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1532
  · change cPayment 1533 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1533+point (1327/200) 4096 1534)/2)
    have hp : cPayment 1533 = (79538429253:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1533+point (1327/200) 4096 1534)/2 = (4893109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1533
  · change cPayment 1534 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1534+point (1327/200) 4096 1535)/2)
    have hp : cPayment 1534 = (79521718316:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1534+point (1327/200) 4096 1535)/2 = (4894163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1534
  · change cPayment 1535 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1535+point (1327/200) 4096 1536)/2)
    have hp : cPayment 1535 = (79504973461:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1535+point (1327/200) 4096 1536)/2 = (4895217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1535
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_095
