import WR2ClassicalCPayments
import WR2ClassicalCPoints019
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_019 (j : Fin 16) : cPayment (16*19+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*19+j.val)+point (1327/200) 4096 (16*19+j.val+1))/2) := by
  fin_cases j
  · change cPayment 304 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 304+point (1327/200) 4096 305)/2)
    have hp : cPayment 304 = (46201687784:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 304+point (1327/200) 4096 305)/2 = (3597743:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_304
  · change cPayment 305 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 305+point (1327/200) 4096 306)/2)
    have hp : cPayment 305 = (46310569743:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 305+point (1327/200) 4096 306)/2 = (3598797:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_305
  · change cPayment 306 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 306+point (1327/200) 4096 307)/2)
    have hp : cPayment 306 = (46419218171:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 306+point (1327/200) 4096 307)/2 = (3599851:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_306
  · change cPayment 307 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 307+point (1327/200) 4096 308)/2)
    have hp : cPayment 307 = (46527633462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 307+point (1327/200) 4096 308)/2 = (720181:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_307
  · change cPayment 308 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 308+point (1327/200) 4096 309)/2)
    have hp : cPayment 308 = (46635816007:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 308+point (1327/200) 4096 309)/2 = (3601959:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_308
  · change cPayment 309 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 309+point (1327/200) 4096 310)/2)
    have hp : cPayment 309 = (46743766198:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 309+point (1327/200) 4096 310)/2 = (3603013:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_309
  · change cPayment 310 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 310+point (1327/200) 4096 311)/2)
    have hp : cPayment 310 = (46851484426:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 310+point (1327/200) 4096 311)/2 = (3604067:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_310
  · change cPayment 311 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 311+point (1327/200) 4096 312)/2)
    have hp : cPayment 311 = (46958971081:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 311+point (1327/200) 4096 312)/2 = (3605121:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_311
  · change cPayment 312 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 312+point (1327/200) 4096 313)/2)
    have hp : cPayment 312 = (47066226551:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 312+point (1327/200) 4096 313)/2 = (144247:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_312
  · change cPayment 313 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 313+point (1327/200) 4096 314)/2)
    have hp : cPayment 313 = (47173251226:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 313+point (1327/200) 4096 314)/2 = (3607229:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_313
  · change cPayment 314 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 314+point (1327/200) 4096 315)/2)
    have hp : cPayment 314 = (47280045492:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 314+point (1327/200) 4096 315)/2 = (3608283:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_314
  · change cPayment 315 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 315+point (1327/200) 4096 316)/2)
    have hp : cPayment 315 = (47386609738:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 315+point (1327/200) 4096 316)/2 = (3609337:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_315
  · change cPayment 316 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 316+point (1327/200) 4096 317)/2)
    have hp : cPayment 316 = (47492944348:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 316+point (1327/200) 4096 317)/2 = (3610391:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_316
  · change cPayment 317 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 317+point (1327/200) 4096 318)/2)
    have hp : cPayment 317 = (47599049709:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 317+point (1327/200) 4096 318)/2 = (722289:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_317
  · change cPayment 318 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 318+point (1327/200) 4096 319)/2)
    have hp : cPayment 318 = (47704926206:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 318+point (1327/200) 4096 319)/2 = (3612499:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_318
  · change cPayment 319 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 319+point (1327/200) 4096 320)/2)
    have hp : cPayment 319 = (47810574221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 319+point (1327/200) 4096 320)/2 = (3613553:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_319
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_019
