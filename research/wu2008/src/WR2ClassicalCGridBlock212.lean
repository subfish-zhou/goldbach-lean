import WR2ClassicalCPayments
import WR2ClassicalCPoints212
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_212 (j : Fin 16) : cPayment (16*212+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*212+j.val)+point (1327/200) 4096 (16*212+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3392 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3392+point (1327/200) 4096 3393)/2)
    have hp : cPayment 3392 = (23173464570:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3392+point (1327/200) 4096 3393)/2 = (1370499:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3392
  · change cPayment 3393 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3393+point (1327/200) 4096 3394)/2)
    have hp : cPayment 3393 = (23139589136:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3393+point (1327/200) 4096 3394)/2 = (6853549:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3393
  · change cPayment 3394 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3394+point (1327/200) 4096 3395)/2)
    have hp : cPayment 3394 = (23105715575:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3394+point (1327/200) 4096 3395)/2 = (6854603:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3394
  · change cPayment 3395 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3395+point (1327/200) 4096 3396)/2)
    have hp : cPayment 3395 = (23071843892:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3395+point (1327/200) 4096 3396)/2 = (6855657:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3395
  · change cPayment 3396 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3396+point (1327/200) 4096 3397)/2)
    have hp : cPayment 3396 = (23037974090:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3396+point (1327/200) 4096 3397)/2 = (6856711:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3396
  · change cPayment 3397 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3397+point (1327/200) 4096 3398)/2)
    have hp : cPayment 3397 = (23004106175:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3397+point (1327/200) 4096 3398)/2 = (1371553:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3397
  · change cPayment 3398 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3398+point (1327/200) 4096 3399)/2)
    have hp : cPayment 3398 = (22970240151:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3398+point (1327/200) 4096 3399)/2 = (6858819:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3398
  · change cPayment 3399 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3399+point (1327/200) 4096 3400)/2)
    have hp : cPayment 3399 = (22936376021:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3399+point (1327/200) 4096 3400)/2 = (6859873:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3399
  · change cPayment 3400 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3400+point (1327/200) 4096 3401)/2)
    have hp : cPayment 3400 = (22902513790:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3400+point (1327/200) 4096 3401)/2 = (6860927:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3400
  · change cPayment 3401 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3401+point (1327/200) 4096 3402)/2)
    have hp : cPayment 3401 = (22868653462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3401+point (1327/200) 4096 3402)/2 = (6861981:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3401
  · change cPayment 3402 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3402+point (1327/200) 4096 3403)/2)
    have hp : cPayment 3402 = (22834795042:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3402+point (1327/200) 4096 3403)/2 = (1372607:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3402
  · change cPayment 3403 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3403+point (1327/200) 4096 3404)/2)
    have hp : cPayment 3403 = (22800938533:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3403+point (1327/200) 4096 3404)/2 = (6864089:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3403
  · change cPayment 3404 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3404+point (1327/200) 4096 3405)/2)
    have hp : cPayment 3404 = (22767083940:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3404+point (1327/200) 4096 3405)/2 = (6865143:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3404
  · change cPayment 3405 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3405+point (1327/200) 4096 3406)/2)
    have hp : cPayment 3405 = (22733231267:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3405+point (1327/200) 4096 3406)/2 = (6866197:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3405
  · change cPayment 3406 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3406+point (1327/200) 4096 3407)/2)
    have hp : cPayment 3406 = (22699380519:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3406+point (1327/200) 4096 3407)/2 = (6867251:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3406
  · change cPayment 3407 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3407+point (1327/200) 4096 3408)/2)
    have hp : cPayment 3407 = (22665531699:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3407+point (1327/200) 4096 3408)/2 = (1373661:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3407
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_212
