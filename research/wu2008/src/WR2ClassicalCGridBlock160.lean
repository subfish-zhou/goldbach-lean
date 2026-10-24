import WR2ClassicalCPayments
import WR2ClassicalCPoints160
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_160 (j : Fin 16) : cPayment (16*160+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*160+j.val)+point (1327/200) 4096 (16*160+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2560 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2560+point (1327/200) 4096 2561)/2)
    have hp : cPayment 2560 = (51443836816:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2560+point (1327/200) 4096 2561)/2 = (5975567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2560
  · change cPayment 2561 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2561+point (1327/200) 4096 2562)/2)
    have hp : cPayment 2561 = (51410653125:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2561+point (1327/200) 4096 2562)/2 = (5976621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2561
  · change cPayment 2562 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2562+point (1327/200) 4096 2563)/2)
    have hp : cPayment 2562 = (51377464699:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2562+point (1327/200) 4096 2563)/2 = (239107:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2562
  · change cPayment 2563 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2563+point (1327/200) 4096 2564)/2)
    have hp : cPayment 2563 = (51344271552:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2563+point (1327/200) 4096 2564)/2 = (5978729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2563
  · change cPayment 2564 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2564+point (1327/200) 4096 2565)/2)
    have hp : cPayment 2564 = (51311073696:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2564+point (1327/200) 4096 2565)/2 = (5979783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2564
  · change cPayment 2565 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2565+point (1327/200) 4096 2566)/2)
    have hp : cPayment 2565 = (51277871145:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2565+point (1327/200) 4096 2566)/2 = (5980837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2565
  · change cPayment 2566 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2566+point (1327/200) 4096 2567)/2)
    have hp : cPayment 2566 = (51244663912:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2566+point (1327/200) 4096 2567)/2 = (5981891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2566
  · change cPayment 2567 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2567+point (1327/200) 4096 2568)/2)
    have hp : cPayment 2567 = (51211452009:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2567+point (1327/200) 4096 2568)/2 = (1196589:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2567
  · change cPayment 2568 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2568+point (1327/200) 4096 2569)/2)
    have hp : cPayment 2568 = (51178235450:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2568+point (1327/200) 4096 2569)/2 = (5983999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2568
  · change cPayment 2569 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2569+point (1327/200) 4096 2570)/2)
    have hp : cPayment 2569 = (51145014248:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2569+point (1327/200) 4096 2570)/2 = (5985053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2569
  · change cPayment 2570 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2570+point (1327/200) 4096 2571)/2)
    have hp : cPayment 2570 = (51111788416:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2570+point (1327/200) 4096 2571)/2 = (5986107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2570
  · change cPayment 2571 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2571+point (1327/200) 4096 2572)/2)
    have hp : cPayment 2571 = (51078557967:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2571+point (1327/200) 4096 2572)/2 = (5987161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2571
  · change cPayment 2572 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2572+point (1327/200) 4096 2573)/2)
    have hp : cPayment 2572 = (51045322914:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2572+point (1327/200) 4096 2573)/2 = (1197643:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2572
  · change cPayment 2573 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2573+point (1327/200) 4096 2574)/2)
    have hp : cPayment 2573 = (51012083269:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2573+point (1327/200) 4096 2574)/2 = (5989269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2573
  · change cPayment 2574 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2574+point (1327/200) 4096 2575)/2)
    have hp : cPayment 2574 = (50978839047:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2574+point (1327/200) 4096 2575)/2 = (5990323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2574
  · change cPayment 2575 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2575+point (1327/200) 4096 2576)/2)
    have hp : cPayment 2575 = (50945590259:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2575+point (1327/200) 4096 2576)/2 = (5991377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2575
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_160
