import WR2ClassicalCPayments
import WR2ClassicalCPoints204
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_204 (j : Fin 16) : cPayment (16*204+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*204+j.val)+point (1327/200) 4096 (16*204+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3264 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3264+point (1327/200) 4096 3265)/2)
    have hp : cPayment 3264 = (27523385396:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3264+point (1327/200) 4096 3265)/2 = (6717583:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3264
  · change cPayment 3265 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3265+point (1327/200) 4096 3266)/2)
    have hp : cPayment 3265 = (27489307689:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3265+point (1327/200) 4096 3266)/2 = (6718637:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3265
  · change cPayment 3266 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3266+point (1327/200) 4096 3267)/2)
    have hp : cPayment 3266 = (27455231255:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3266+point (1327/200) 4096 3267)/2 = (6719691:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3266
  · change cPayment 3267 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3267+point (1327/200) 4096 3268)/2)
    have hp : cPayment 3267 = (27421156101:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3267+point (1327/200) 4096 3268)/2 = (1344149:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3267
  · change cPayment 3268 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3268+point (1327/200) 4096 3269)/2)
    have hp : cPayment 3268 = (27387082231:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3268+point (1327/200) 4096 3269)/2 = (6721799:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3268
  · change cPayment 3269 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3269+point (1327/200) 4096 3270)/2)
    have hp : cPayment 3269 = (27353009650:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3269+point (1327/200) 4096 3270)/2 = (6722853:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3269
  · change cPayment 3270 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3270+point (1327/200) 4096 3271)/2)
    have hp : cPayment 3270 = (27318938363:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3270+point (1327/200) 4096 3271)/2 = (6723907:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3270
  · change cPayment 3271 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3271+point (1327/200) 4096 3272)/2)
    have hp : cPayment 3271 = (27284868376:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3271+point (1327/200) 4096 3272)/2 = (6724961:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3271
  · change cPayment 3272 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3272+point (1327/200) 4096 3273)/2)
    have hp : cPayment 3272 = (27250799693:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3272+point (1327/200) 4096 3273)/2 = (1345203:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3272
  · change cPayment 3273 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3273+point (1327/200) 4096 3274)/2)
    have hp : cPayment 3273 = (27216732320:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3273+point (1327/200) 4096 3274)/2 = (6727069:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3273
  · change cPayment 3274 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3274+point (1327/200) 4096 3275)/2)
    have hp : cPayment 3274 = (27182666262:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3274+point (1327/200) 4096 3275)/2 = (6728123:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3274
  · change cPayment 3275 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3275+point (1327/200) 4096 3276)/2)
    have hp : cPayment 3275 = (27148601523:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3275+point (1327/200) 4096 3276)/2 = (6729177:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3275
  · change cPayment 3276 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3276+point (1327/200) 4096 3277)/2)
    have hp : cPayment 3276 = (27114538109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3276+point (1327/200) 4096 3277)/2 = (6730231:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3276
  · change cPayment 3277 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3277+point (1327/200) 4096 3278)/2)
    have hp : cPayment 3277 = (27080476024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3277+point (1327/200) 4096 3278)/2 = (1346257:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3277
  · change cPayment 3278 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3278+point (1327/200) 4096 3279)/2)
    have hp : cPayment 3278 = (27046415274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3278+point (1327/200) 4096 3279)/2 = (6732339:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3278
  · change cPayment 3279 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3279+point (1327/200) 4096 3280)/2)
    have hp : cPayment 3279 = (27012355865:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3279+point (1327/200) 4096 3280)/2 = (6733393:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3279
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_204
