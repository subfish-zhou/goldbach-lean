import WR2ClassicalCPayments
import WR2ClassicalCPoints152
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_152 (j : Fin 16) : cPayment (16*152+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*152+j.val)+point (1327/200) 4096 (16*152+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2432 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2432+point (1327/200) 4096 2433)/2)
    have hp : cPayment 2432 = (55647346127:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2432+point (1327/200) 4096 2433)/2 = (1168131:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2432
  · change cPayment 2433 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2433+point (1327/200) 4096 2434)/2)
    have hp : cPayment 2433 = (55614883491:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2433+point (1327/200) 4096 2434)/2 = (5841709:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2433
  · change cPayment 2434 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2434+point (1327/200) 4096 2435)/2)
    have hp : cPayment 2434 = (55582414287:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2434+point (1327/200) 4096 2435)/2 = (5842763:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2434
  · change cPayment 2435 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2435+point (1327/200) 4096 2436)/2)
    have hp : cPayment 2435 = (55549938528:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2435+point (1327/200) 4096 2436)/2 = (5843817:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2435
  · change cPayment 2436 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2436+point (1327/200) 4096 2437)/2)
    have hp : cPayment 2436 = (55517456232:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2436+point (1327/200) 4096 2437)/2 = (5844871:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2436
  · change cPayment 2437 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2437+point (1327/200) 4096 2438)/2)
    have hp : cPayment 2437 = (55484967413:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2437+point (1327/200) 4096 2438)/2 = (233837:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2437
  · change cPayment 2438 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2438+point (1327/200) 4096 2439)/2)
    have hp : cPayment 2438 = (55452472087:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2438+point (1327/200) 4096 2439)/2 = (5846979:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2438
  · change cPayment 2439 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2439+point (1327/200) 4096 2440)/2)
    have hp : cPayment 2439 = (55419970269:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2439+point (1327/200) 4096 2440)/2 = (5848033:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2439
  · change cPayment 2440 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2440+point (1327/200) 4096 2441)/2)
    have hp : cPayment 2440 = (55387461975:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2440+point (1327/200) 4096 2441)/2 = (5849087:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2440
  · change cPayment 2441 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2441+point (1327/200) 4096 2442)/2)
    have hp : cPayment 2441 = (55354947221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2441+point (1327/200) 4096 2442)/2 = (5850141:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2441
  · change cPayment 2442 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2442+point (1327/200) 4096 2443)/2)
    have hp : cPayment 2442 = (55322426021:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2442+point (1327/200) 4096 2443)/2 = (1170239:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2442
  · change cPayment 2443 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2443+point (1327/200) 4096 2444)/2)
    have hp : cPayment 2443 = (55289898391:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2443+point (1327/200) 4096 2444)/2 = (5852249:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2443
  · change cPayment 2444 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2444+point (1327/200) 4096 2445)/2)
    have hp : cPayment 2444 = (55257364347:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2444+point (1327/200) 4096 2445)/2 = (5853303:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2444
  · change cPayment 2445 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2445+point (1327/200) 4096 2446)/2)
    have hp : cPayment 2445 = (55224823904:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2445+point (1327/200) 4096 2446)/2 = (5854357:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2445
  · change cPayment 2446 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2446+point (1327/200) 4096 2447)/2)
    have hp : cPayment 2446 = (55192277077:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2446+point (1327/200) 4096 2447)/2 = (5855411:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2446
  · change cPayment 2447 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2447+point (1327/200) 4096 2448)/2)
    have hp : cPayment 2447 = (55159723882:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2447+point (1327/200) 4096 2448)/2 = (1171293:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2447
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_152
