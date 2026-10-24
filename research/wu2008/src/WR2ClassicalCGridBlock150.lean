import WR2ClassicalCPayments
import WR2ClassicalCPoints150
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_150 (j : Fin 16) : cPayment (16*150+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*150+j.val)+point (1327/200) 4096 (16*150+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2400 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2400+point (1327/200) 4096 2401)/2)
    have hp : cPayment 2400 = (56682587627:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2400+point (1327/200) 4096 2401)/2 = (5806927:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2400
  · change cPayment 2401 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2401+point (1327/200) 4096 2402)/2)
    have hp : cPayment 2401 = (56650343555:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2401+point (1327/200) 4096 2402)/2 = (5807981:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2401
  · change cPayment 2402 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2402+point (1327/200) 4096 2403)/2)
    have hp : cPayment 2402 = (56618092404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2402+point (1327/200) 4096 2403)/2 = (1161807:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2402
  · change cPayment 2403 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2403+point (1327/200) 4096 2404)/2)
    have hp : cPayment 2403 = (56585834190:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2403+point (1327/200) 4096 2404)/2 = (5810089:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2403
  · change cPayment 2404 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2404+point (1327/200) 4096 2405)/2)
    have hp : cPayment 2404 = (56553568930:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2404+point (1327/200) 4096 2405)/2 = (5811143:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2404
  · change cPayment 2405 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2405+point (1327/200) 4096 2406)/2)
    have hp : cPayment 2405 = (56521296640:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2405+point (1327/200) 4096 2406)/2 = (5812197:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2405
  · change cPayment 2406 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2406+point (1327/200) 4096 2407)/2)
    have hp : cPayment 2406 = (56489017337:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2406+point (1327/200) 4096 2407)/2 = (5813251:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2406
  · change cPayment 2407 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2407+point (1327/200) 4096 2408)/2)
    have hp : cPayment 2407 = (56456731036:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2407+point (1327/200) 4096 2408)/2 = (1162861:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2407
  · change cPayment 2408 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2408+point (1327/200) 4096 2409)/2)
    have hp : cPayment 2408 = (56424437753:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2408+point (1327/200) 4096 2409)/2 = (5815359:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2408
  · change cPayment 2409 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2409+point (1327/200) 4096 2410)/2)
    have hp : cPayment 2409 = (56392137505:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2409+point (1327/200) 4096 2410)/2 = (5816413:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2409
  · change cPayment 2410 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2410+point (1327/200) 4096 2411)/2)
    have hp : cPayment 2410 = (56359830308:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2410+point (1327/200) 4096 2411)/2 = (5817467:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2410
  · change cPayment 2411 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2411+point (1327/200) 4096 2412)/2)
    have hp : cPayment 2411 = (56327516178:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2411+point (1327/200) 4096 2412)/2 = (5818521:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2411
  · change cPayment 2412 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2412+point (1327/200) 4096 2413)/2)
    have hp : cPayment 2412 = (56295195131:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2412+point (1327/200) 4096 2413)/2 = (232783:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2412
  · change cPayment 2413 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2413+point (1327/200) 4096 2414)/2)
    have hp : cPayment 2413 = (56262867182:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2413+point (1327/200) 4096 2414)/2 = (5820629:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2413
  · change cPayment 2414 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2414+point (1327/200) 4096 2415)/2)
    have hp : cPayment 2414 = (56230532349:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2414+point (1327/200) 4096 2415)/2 = (5821683:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2414
  · change cPayment 2415 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2415+point (1327/200) 4096 2416)/2)
    have hp : cPayment 2415 = (56198190646:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2415+point (1327/200) 4096 2416)/2 = (5822737:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2415
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_150
