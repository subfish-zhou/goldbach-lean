import WR2ClassicalCPayments
import WR2ClassicalCPoints146
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_146 (j : Fin 16) : cPayment (16*146+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*146+j.val)+point (1327/200) 4096 (16*146+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2336 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2336+point (1327/200) 4096 2337)/2)
    have hp : cPayment 2336 = (58730724389:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2336+point (1327/200) 4096 2337)/2 = (5739471:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2336
  · change cPayment 2337 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2337+point (1327/200) 4096 2338)/2)
    have hp : cPayment 2337 = (58698968154:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2337+point (1327/200) 4096 2338)/2 = (229621:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2337
  · change cPayment 2338 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2338+point (1327/200) 4096 2339)/2)
    have hp : cPayment 2338 = (58667203754:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2338+point (1327/200) 4096 2339)/2 = (5741579:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2338
  · change cPayment 2339 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2339+point (1327/200) 4096 2340)/2)
    have hp : cPayment 2339 = (58635431208:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2339+point (1327/200) 4096 2340)/2 = (5742633:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2339
  · change cPayment 2340 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2340+point (1327/200) 4096 2341)/2)
    have hp : cPayment 2340 = (58603650531:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2340+point (1327/200) 4096 2341)/2 = (5743687:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2340
  · change cPayment 2341 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2341+point (1327/200) 4096 2342)/2)
    have hp : cPayment 2341 = (58571861744:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2341+point (1327/200) 4096 2342)/2 = (5744741:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2341
  · change cPayment 2342 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2342+point (1327/200) 4096 2343)/2)
    have hp : cPayment 2342 = (58540064862:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2342+point (1327/200) 4096 2343)/2 = (1149159:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2342
  · change cPayment 2343 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2343+point (1327/200) 4096 2344)/2)
    have hp : cPayment 2343 = (58508259903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2343+point (1327/200) 4096 2344)/2 = (5746849:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2343
  · change cPayment 2344 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2344+point (1327/200) 4096 2345)/2)
    have hp : cPayment 2344 = (58476446886:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2344+point (1327/200) 4096 2345)/2 = (5747903:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2344
  · change cPayment 2345 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2345+point (1327/200) 4096 2346)/2)
    have hp : cPayment 2345 = (58444625827:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2345+point (1327/200) 4096 2346)/2 = (5748957:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2345
  · change cPayment 2346 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2346+point (1327/200) 4096 2347)/2)
    have hp : cPayment 2346 = (58412796744:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2346+point (1327/200) 4096 2347)/2 = (5750011:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2346
  · change cPayment 2347 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2347+point (1327/200) 4096 2348)/2)
    have hp : cPayment 2347 = (58380959655:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2347+point (1327/200) 4096 2348)/2 = (1150213:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2347
  · change cPayment 2348 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2348+point (1327/200) 4096 2349)/2)
    have hp : cPayment 2348 = (58349114577:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2348+point (1327/200) 4096 2349)/2 = (5752119:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2348
  · change cPayment 2349 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2349+point (1327/200) 4096 2350)/2)
    have hp : cPayment 2349 = (58317261528:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2349+point (1327/200) 4096 2350)/2 = (5753173:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2349
  · change cPayment 2350 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2350+point (1327/200) 4096 2351)/2)
    have hp : cPayment 2350 = (58285400525:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2350+point (1327/200) 4096 2351)/2 = (5754227:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2350
  · change cPayment 2351 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2351+point (1327/200) 4096 2352)/2)
    have hp : cPayment 2351 = (58253531585:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2351+point (1327/200) 4096 2352)/2 = (5755281:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2351
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_146
