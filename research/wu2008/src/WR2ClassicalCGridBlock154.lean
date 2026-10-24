import WR2ClassicalCPayments
import WR2ClassicalCPoints154
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_154 (j : Fin 16) : cPayment (16*154+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*154+j.val)+point (1327/200) 4096 (16*154+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2464 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2464+point (1327/200) 4096 2465)/2)
    have hp : cPayment 2464 = (54605359950:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2464+point (1327/200) 4096 2465)/2 = (5874383:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2464
  · change cPayment 2465 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2465+point (1327/200) 4096 2466)/2)
    have hp : cPayment 2465 = (54572694722:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2465+point (1327/200) 4096 2466)/2 = (5875437:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2465
  · change cPayment 2466 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2466+point (1327/200) 4096 2467)/2)
    have hp : cPayment 2466 = (54540023412:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2466+point (1327/200) 4096 2467)/2 = (5876491:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2466
  · change cPayment 2467 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2467+point (1327/200) 4096 2468)/2)
    have hp : cPayment 2467 = (54507346036:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2467+point (1327/200) 4096 2468)/2 = (1175509:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2467
  · change cPayment 2468 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2468+point (1327/200) 4096 2469)/2)
    have hp : cPayment 2468 = (54474662609:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2468+point (1327/200) 4096 2469)/2 = (5878599:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2468
  · change cPayment 2469 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2469+point (1327/200) 4096 2470)/2)
    have hp : cPayment 2469 = (54441973145:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2469+point (1327/200) 4096 2470)/2 = (5879653:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2469
  · change cPayment 2470 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2470+point (1327/200) 4096 2471)/2)
    have hp : cPayment 2470 = (54409277660:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2470+point (1327/200) 4096 2471)/2 = (5880707:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2470
  · change cPayment 2471 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2471+point (1327/200) 4096 2472)/2)
    have hp : cPayment 2471 = (54376576169:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2471+point (1327/200) 4096 2472)/2 = (5881761:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2471
  · change cPayment 2472 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2472+point (1327/200) 4096 2473)/2)
    have hp : cPayment 2472 = (54343868686:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2472+point (1327/200) 4096 2473)/2 = (1176563:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2472
  · change cPayment 2473 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2473+point (1327/200) 4096 2474)/2)
    have hp : cPayment 2473 = (54311155225:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2473+point (1327/200) 4096 2474)/2 = (5883869:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2473
  · change cPayment 2474 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2474+point (1327/200) 4096 2475)/2)
    have hp : cPayment 2474 = (54278435803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2474+point (1327/200) 4096 2475)/2 = (5884923:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2474
  · change cPayment 2475 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2475+point (1327/200) 4096 2476)/2)
    have hp : cPayment 2475 = (54245710433:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2475+point (1327/200) 4096 2476)/2 = (5885977:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2475
  · change cPayment 2476 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2476+point (1327/200) 4096 2477)/2)
    have hp : cPayment 2476 = (54212979131:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2476+point (1327/200) 4096 2477)/2 = (5887031:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2476
  · change cPayment 2477 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2477+point (1327/200) 4096 2478)/2)
    have hp : cPayment 2477 = (54180241910:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2477+point (1327/200) 4096 2478)/2 = (1177617:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2477
  · change cPayment 2478 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2478+point (1327/200) 4096 2479)/2)
    have hp : cPayment 2478 = (54147498786:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2478+point (1327/200) 4096 2479)/2 = (5889139:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2478
  · change cPayment 2479 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2479+point (1327/200) 4096 2480)/2)
    have hp : cPayment 2479 = (54114749774:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2479+point (1327/200) 4096 2480)/2 = (5890193:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2479
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_154
