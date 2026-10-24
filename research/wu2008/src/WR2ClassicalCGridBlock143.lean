import WR2ClassicalCPayments
import WR2ClassicalCPoints143
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_143 (j : Fin 16) : cPayment (16*143+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*143+j.val)+point (1327/200) 4096 (16*143+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2288 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2288+point (1327/200) 4096 2289)/2)
    have hp : cPayment 2288 = (60245069224:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2288+point (1327/200) 4096 2289)/2 = (5688879:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2288
  · change cPayment 2289 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2289+point (1327/200) 4096 2290)/2)
    have hp : cPayment 2289 = (60213726171:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2289+point (1327/200) 4096 2290)/2 = (5689933:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2289
  · change cPayment 2290 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2290+point (1327/200) 4096 2291)/2)
    have hp : cPayment 2290 = (60182374075:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2290+point (1327/200) 4096 2291)/2 = (5690987:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2290
  · change cPayment 2291 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2291+point (1327/200) 4096 2292)/2)
    have hp : cPayment 2291 = (60151012956:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2291+point (1327/200) 4096 2292)/2 = (5692041:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2291
  · change cPayment 2292 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2292+point (1327/200) 4096 2293)/2)
    have hp : cPayment 2292 = (60119642833:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2292+point (1327/200) 4096 2293)/2 = (1138619:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2292
  · change cPayment 2293 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2293+point (1327/200) 4096 2294)/2)
    have hp : cPayment 2293 = (60088263724:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2293+point (1327/200) 4096 2294)/2 = (5694149:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2293
  · change cPayment 2294 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2294+point (1327/200) 4096 2295)/2)
    have hp : cPayment 2294 = (60056875648:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2294+point (1327/200) 4096 2295)/2 = (5695203:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2294
  · change cPayment 2295 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2295+point (1327/200) 4096 2296)/2)
    have hp : cPayment 2295 = (60025478624:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2295+point (1327/200) 4096 2296)/2 = (5696257:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2295
  · change cPayment 2296 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2296+point (1327/200) 4096 2297)/2)
    have hp : cPayment 2296 = (59994072670:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2296+point (1327/200) 4096 2297)/2 = (5697311:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2296
  · change cPayment 2297 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2297+point (1327/200) 4096 2298)/2)
    have hp : cPayment 2297 = (59962657805:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2297+point (1327/200) 4096 2298)/2 = (1139673:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2297
  · change cPayment 2298 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2298+point (1327/200) 4096 2299)/2)
    have hp : cPayment 2298 = (59931234049:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2298+point (1327/200) 4096 2299)/2 = (5699419:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2298
  · change cPayment 2299 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2299+point (1327/200) 4096 2300)/2)
    have hp : cPayment 2299 = (59899801419:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2299+point (1327/200) 4096 2300)/2 = (5700473:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2299
  · change cPayment 2300 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2300+point (1327/200) 4096 2301)/2)
    have hp : cPayment 2300 = (59868359934:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2300+point (1327/200) 4096 2301)/2 = (5701527:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2300
  · change cPayment 2301 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2301+point (1327/200) 4096 2302)/2)
    have hp : cPayment 2301 = (59836909613:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2301+point (1327/200) 4096 2302)/2 = (5702581:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2301
  · change cPayment 2302 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2302+point (1327/200) 4096 2303)/2)
    have hp : cPayment 2302 = (59805450475:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2302+point (1327/200) 4096 2303)/2 = (1140727:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2302
  · change cPayment 2303 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2303+point (1327/200) 4096 2304)/2)
    have hp : cPayment 2303 = (59773982537:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2303+point (1327/200) 4096 2304)/2 = (5704689:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2303
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_143
