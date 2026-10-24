import WR2ClassicalCPayments
import WR2ClassicalCPoints153
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_153 (j : Fin 16) : cPayment (16*153+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*153+j.val)+point (1327/200) 4096 (16*153+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2448 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2448+point (1327/200) 4096 2449)/2)
    have hp : cPayment 2448 = (55127164334:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2448+point (1327/200) 4096 2449)/2 = (5857519:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2448
  · change cPayment 2449 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2449+point (1327/200) 4096 2450)/2)
    have hp : cPayment 2449 = (55094598448:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2449+point (1327/200) 4096 2450)/2 = (5858573:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2449
  · change cPayment 2450 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2450+point (1327/200) 4096 2451)/2)
    have hp : cPayment 2450 = (55062026239:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2450+point (1327/200) 4096 2451)/2 = (5859627:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2450
  · change cPayment 2451 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2451+point (1327/200) 4096 2452)/2)
    have hp : cPayment 2451 = (55029447723:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2451+point (1327/200) 4096 2452)/2 = (5860681:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2451
  · change cPayment 2452 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2452+point (1327/200) 4096 2453)/2)
    have hp : cPayment 2452 = (54996862915:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2452+point (1327/200) 4096 2453)/2 = (1172347:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2452
  · change cPayment 2453 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2453+point (1327/200) 4096 2454)/2)
    have hp : cPayment 2453 = (54964271830:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2453+point (1327/200) 4096 2454)/2 = (5862789:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2453
  · change cPayment 2454 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2454+point (1327/200) 4096 2455)/2)
    have hp : cPayment 2454 = (54931674483:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2454+point (1327/200) 4096 2455)/2 = (5863843:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2454
  · change cPayment 2455 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2455+point (1327/200) 4096 2456)/2)
    have hp : cPayment 2455 = (54899070890:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2455+point (1327/200) 4096 2456)/2 = (5864897:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2455
  · change cPayment 2456 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2456+point (1327/200) 4096 2457)/2)
    have hp : cPayment 2456 = (54866461066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2456+point (1327/200) 4096 2457)/2 = (5865951:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2456
  · change cPayment 2457 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2457+point (1327/200) 4096 2458)/2)
    have hp : cPayment 2457 = (54833845025:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2457+point (1327/200) 4096 2458)/2 = (1173401:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2457
  · change cPayment 2458 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2458+point (1327/200) 4096 2459)/2)
    have hp : cPayment 2458 = (54801222783:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2458+point (1327/200) 4096 2459)/2 = (5868059:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2458
  · change cPayment 2459 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2459+point (1327/200) 4096 2460)/2)
    have hp : cPayment 2459 = (54768594355:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2459+point (1327/200) 4096 2460)/2 = (5869113:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2459
  · change cPayment 2460 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2460+point (1327/200) 4096 2461)/2)
    have hp : cPayment 2460 = (54735959756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2460+point (1327/200) 4096 2461)/2 = (5870167:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2460
  · change cPayment 2461 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2461+point (1327/200) 4096 2462)/2)
    have hp : cPayment 2461 = (54703319001:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2461+point (1327/200) 4096 2462)/2 = (5871221:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2461
  · change cPayment 2462 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2462+point (1327/200) 4096 2463)/2)
    have hp : cPayment 2462 = (54670672105:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2462+point (1327/200) 4096 2463)/2 = (234891:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2462
  · change cPayment 2463 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2463+point (1327/200) 4096 2464)/2)
    have hp : cPayment 2463 = (54638019083:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2463+point (1327/200) 4096 2464)/2 = (5873329:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2463
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_153
