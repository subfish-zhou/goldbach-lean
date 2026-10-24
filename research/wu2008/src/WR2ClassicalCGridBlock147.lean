import WR2ClassicalCPayments
import WR2ClassicalCPoints147
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_147 (j : Fin 16) : cPayment (16*147+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*147+j.val)+point (1327/200) 4096 (16*147+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2352 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2352+point (1327/200) 4096 2353)/2)
    have hp : cPayment 2352 = (58221654726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2352+point (1327/200) 4096 2353)/2 = (1151267:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2352
  · change cPayment 2353 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2353+point (1327/200) 4096 2354)/2)
    have hp : cPayment 2353 = (58189769965:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2353+point (1327/200) 4096 2354)/2 = (5757389:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2353
  · change cPayment 2354 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2354+point (1327/200) 4096 2355)/2)
    have hp : cPayment 2354 = (58157877319:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2354+point (1327/200) 4096 2355)/2 = (5758443:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2354
  · change cPayment 2355 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2355+point (1327/200) 4096 2356)/2)
    have hp : cPayment 2355 = (58125976807:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2355+point (1327/200) 4096 2356)/2 = (5759497:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2355
  · change cPayment 2356 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2356+point (1327/200) 4096 2357)/2)
    have hp : cPayment 2356 = (58094068444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2356+point (1327/200) 4096 2357)/2 = (5760551:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2356
  · change cPayment 2357 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2357+point (1327/200) 4096 2358)/2)
    have hp : cPayment 2357 = (58062152249:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2357+point (1327/200) 4096 2358)/2 = (1152321:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2357
  · change cPayment 2358 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2358+point (1327/200) 4096 2359)/2)
    have hp : cPayment 2358 = (58030228239:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2358+point (1327/200) 4096 2359)/2 = (5762659:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2358
  · change cPayment 2359 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2359+point (1327/200) 4096 2360)/2)
    have hp : cPayment 2359 = (57998296431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2359+point (1327/200) 4096 2360)/2 = (5763713:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2359
  · change cPayment 2360 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2360+point (1327/200) 4096 2361)/2)
    have hp : cPayment 2360 = (57966356841:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2360+point (1327/200) 4096 2361)/2 = (5764767:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2360
  · change cPayment 2361 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2361+point (1327/200) 4096 2362)/2)
    have hp : cPayment 2361 = (57934409488:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2361+point (1327/200) 4096 2362)/2 = (5765821:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2361
  · change cPayment 2362 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2362+point (1327/200) 4096 2363)/2)
    have hp : cPayment 2362 = (57902454389:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2362+point (1327/200) 4096 2363)/2 = (230675:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2362
  · change cPayment 2363 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2363+point (1327/200) 4096 2364)/2)
    have hp : cPayment 2363 = (57870491560:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2363+point (1327/200) 4096 2364)/2 = (5767929:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2363
  · change cPayment 2364 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2364+point (1327/200) 4096 2365)/2)
    have hp : cPayment 2364 = (57838521018:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2364+point (1327/200) 4096 2365)/2 = (5768983:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2364
  · change cPayment 2365 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2365+point (1327/200) 4096 2366)/2)
    have hp : cPayment 2365 = (57806542781:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2365+point (1327/200) 4096 2366)/2 = (5770037:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2365
  · change cPayment 2366 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2366+point (1327/200) 4096 2367)/2)
    have hp : cPayment 2366 = (57774556867:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2366+point (1327/200) 4096 2367)/2 = (5771091:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2366
  · change cPayment 2367 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2367+point (1327/200) 4096 2368)/2)
    have hp : cPayment 2367 = (57742563291:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2367+point (1327/200) 4096 2368)/2 = (1154429:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2367
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_147
