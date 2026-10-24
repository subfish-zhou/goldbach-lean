import WR2ClassicalCPayments
import WR2ClassicalCPoints149
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_149 (j : Fin 16) : cPayment (16*149+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*149+j.val)+point (1327/200) 4096 (16*149+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2384 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2384+point (1327/200) 4096 2385)/2)
    have hp : cPayment 2384 = (57197516755:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2384+point (1327/200) 4096 2385)/2 = (5790063:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2384
  · change cPayment 2385 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2385+point (1327/200) 4096 2386)/2)
    have hp : cPayment 2385 = (57165388167:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2385+point (1327/200) 4096 2386)/2 = (5791117:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2385
  · change cPayment 2386 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2386+point (1327/200) 4096 2387)/2)
    have hp : cPayment 2386 = (57133252239:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2386+point (1327/200) 4096 2387)/2 = (5792171:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2386
  · change cPayment 2387 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2387+point (1327/200) 4096 2388)/2)
    have hp : cPayment 2387 = (57101108985:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2387+point (1327/200) 4096 2388)/2 = (231729:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2387
  · change cPayment 2388 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2388+point (1327/200) 4096 2389)/2)
    have hp : cPayment 2388 = (57068958423:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2388+point (1327/200) 4096 2389)/2 = (5794279:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2388
  · change cPayment 2389 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2389+point (1327/200) 4096 2390)/2)
    have hp : cPayment 2389 = (57036800569:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2389+point (1327/200) 4096 2390)/2 = (5795333:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2389
  · change cPayment 2390 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2390+point (1327/200) 4096 2391)/2)
    have hp : cPayment 2390 = (57004635440:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2390+point (1327/200) 4096 2391)/2 = (5796387:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2390
  · change cPayment 2391 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2391+point (1327/200) 4096 2392)/2)
    have hp : cPayment 2391 = (56972463052:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2391+point (1327/200) 4096 2392)/2 = (5797441:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2391
  · change cPayment 2392 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2392+point (1327/200) 4096 2393)/2)
    have hp : cPayment 2392 = (56940283421:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2392+point (1327/200) 4096 2393)/2 = (1159699:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2392
  · change cPayment 2393 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2393+point (1327/200) 4096 2394)/2)
    have hp : cPayment 2393 = (56908096565:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2393+point (1327/200) 4096 2394)/2 = (5799549:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2393
  · change cPayment 2394 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2394+point (1327/200) 4096 2395)/2)
    have hp : cPayment 2394 = (56875902500:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2394+point (1327/200) 4096 2395)/2 = (5800603:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2394
  · change cPayment 2395 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2395+point (1327/200) 4096 2396)/2)
    have hp : cPayment 2395 = (56843701241:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2395+point (1327/200) 4096 2396)/2 = (5801657:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2395
  · change cPayment 2396 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2396+point (1327/200) 4096 2397)/2)
    have hp : cPayment 2396 = (56811492806:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2396+point (1327/200) 4096 2397)/2 = (5802711:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2396
  · change cPayment 2397 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2397+point (1327/200) 4096 2398)/2)
    have hp : cPayment 2397 = (56779277211:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2397+point (1327/200) 4096 2398)/2 = (1160753:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2397
  · change cPayment 2398 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2398+point (1327/200) 4096 2399)/2)
    have hp : cPayment 2398 = (56747054472:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2398+point (1327/200) 4096 2399)/2 = (5804819:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2398
  · change cPayment 2399 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2399+point (1327/200) 4096 2400)/2)
    have hp : cPayment 2399 = (56714824605:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2399+point (1327/200) 4096 2400)/2 = (5805873:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2399
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_149
