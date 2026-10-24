import WR2ClassicalCPayments
import WR2ClassicalCPoints151
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_151 (j : Fin 16) : cPayment (16*151+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*151+j.val)+point (1327/200) 4096 (16*151+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2416 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2416+point (1327/200) 4096 2417)/2)
    have hp : cPayment 2416 = (56165842090:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2416+point (1327/200) 4096 2417)/2 = (5823791:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2416
  · change cPayment 2417 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2417+point (1327/200) 4096 2418)/2)
    have hp : cPayment 2417 = (56133486697:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2417+point (1327/200) 4096 2418)/2 = (1164969:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2417
  · change cPayment 2418 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2418+point (1327/200) 4096 2419)/2)
    have hp : cPayment 2418 = (56101124483:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2418+point (1327/200) 4096 2419)/2 = (5825899:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2418
  · change cPayment 2419 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2419+point (1327/200) 4096 2420)/2)
    have hp : cPayment 2419 = (56068755464:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2419+point (1327/200) 4096 2420)/2 = (5826953:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2419
  · change cPayment 2420 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2420+point (1327/200) 4096 2421)/2)
    have hp : cPayment 2420 = (56036379655:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2420+point (1327/200) 4096 2421)/2 = (5828007:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2420
  · change cPayment 2421 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2421+point (1327/200) 4096 2422)/2)
    have hp : cPayment 2421 = (56003997073:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2421+point (1327/200) 4096 2422)/2 = (5829061:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2421
  · change cPayment 2422 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2422+point (1327/200) 4096 2423)/2)
    have hp : cPayment 2422 = (55971607733:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2422+point (1327/200) 4096 2423)/2 = (1166023:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2422
  · change cPayment 2423 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2423+point (1327/200) 4096 2424)/2)
    have hp : cPayment 2423 = (55939211651:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2423+point (1327/200) 4096 2424)/2 = (5831169:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2423
  · change cPayment 2424 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2424+point (1327/200) 4096 2425)/2)
    have hp : cPayment 2424 = (55906808842:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2424+point (1327/200) 4096 2425)/2 = (5832223:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2424
  · change cPayment 2425 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2425+point (1327/200) 4096 2426)/2)
    have hp : cPayment 2425 = (55874399324:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2425+point (1327/200) 4096 2426)/2 = (5833277:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2425
  · change cPayment 2426 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2426+point (1327/200) 4096 2427)/2)
    have hp : cPayment 2426 = (55841983111:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2426+point (1327/200) 4096 2427)/2 = (5834331:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2426
  · change cPayment 2427 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2427+point (1327/200) 4096 2428)/2)
    have hp : cPayment 2427 = (55809560219:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2427+point (1327/200) 4096 2428)/2 = (1167077:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2427
  · change cPayment 2428 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2428+point (1327/200) 4096 2429)/2)
    have hp : cPayment 2428 = (55777130664:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2428+point (1327/200) 4096 2429)/2 = (5836439:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2428
  · change cPayment 2429 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2429+point (1327/200) 4096 2430)/2)
    have hp : cPayment 2429 = (55744694462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2429+point (1327/200) 4096 2430)/2 = (5837493:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2429
  · change cPayment 2430 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2430+point (1327/200) 4096 2431)/2)
    have hp : cPayment 2430 = (55712251628:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2430+point (1327/200) 4096 2431)/2 = (5838547:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2430
  · change cPayment 2431 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2431+point (1327/200) 4096 2432)/2)
    have hp : cPayment 2431 = (55679802177:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2431+point (1327/200) 4096 2432)/2 = (5839601:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2431
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_151
