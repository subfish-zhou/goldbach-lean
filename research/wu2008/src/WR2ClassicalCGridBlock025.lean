import WR2ClassicalCPayments
import WR2ClassicalCPoints025
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_025 (j : Fin 16) : cPayment (16*25+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*25+j.val)+point (1327/200) 4096 (16*25+j.val+1))/2) := by
  fin_cases j
  · change cPayment 400 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 400+point (1327/200) 4096 401)/2)
    have hp : cPayment 400 = (55643204431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 400+point (1327/200) 4096 401)/2 = (3698927:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_400
  · change cPayment 401 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 401+point (1327/200) 4096 402)/2)
    have hp : cPayment 401 = (55731357368:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 401+point (1327/200) 4096 402)/2 = (3699981:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_401
  · change cPayment 402 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 402+point (1327/200) 4096 403)/2)
    have hp : cPayment 402 = (55819311302:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 402+point (1327/200) 4096 403)/2 = (740207:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_402
  · change cPayment 403 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 403+point (1327/200) 4096 404)/2)
    have hp : cPayment 403 = (55907066563:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 403+point (1327/200) 4096 404)/2 = (3702089:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_403
  · change cPayment 404 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 404+point (1327/200) 4096 405)/2)
    have hp : cPayment 404 = (55994623477:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 404+point (1327/200) 4096 405)/2 = (3703143:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_404
  · change cPayment 405 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 405+point (1327/200) 4096 406)/2)
    have hp : cPayment 405 = (56081982371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 405+point (1327/200) 4096 406)/2 = (3704197:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_405
  · change cPayment 406 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 406+point (1327/200) 4096 407)/2)
    have hp : cPayment 406 = (56169143572:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 406+point (1327/200) 4096 407)/2 = (3705251:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_406
  · change cPayment 407 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 407+point (1327/200) 4096 408)/2)
    have hp : cPayment 407 = (56256107404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 407+point (1327/200) 4096 408)/2 = (741261:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_407
  · change cPayment 408 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 408+point (1327/200) 4096 409)/2)
    have hp : cPayment 408 = (56342874195:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 408+point (1327/200) 4096 409)/2 = (3707359:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_408
  · change cPayment 409 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 409+point (1327/200) 4096 410)/2)
    have hp : cPayment 409 = (56429444266:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 409+point (1327/200) 4096 410)/2 = (3708413:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_409
  · change cPayment 410 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 410+point (1327/200) 4096 411)/2)
    have hp : cPayment 410 = (56515817944:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 410+point (1327/200) 4096 411)/2 = (3709467:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_410
  · change cPayment 411 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 411+point (1327/200) 4096 412)/2)
    have hp : cPayment 411 = (56601995550:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 411+point (1327/200) 4096 412)/2 = (3710521:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_411
  · change cPayment 412 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 412+point (1327/200) 4096 413)/2)
    have hp : cPayment 412 = (56687977408:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 412+point (1327/200) 4096 413)/2 = (148463:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_412
  · change cPayment 413 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 413+point (1327/200) 4096 414)/2)
    have hp : cPayment 413 = (56773763839:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 413+point (1327/200) 4096 414)/2 = (3712629:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_413
  · change cPayment 414 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 414+point (1327/200) 4096 415)/2)
    have hp : cPayment 414 = (56859355165:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 414+point (1327/200) 4096 415)/2 = (3713683:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_414
  · change cPayment 415 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 415+point (1327/200) 4096 416)/2)
    have hp : cPayment 415 = (56944751707:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 415+point (1327/200) 4096 416)/2 = (3714737:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_415
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_025
