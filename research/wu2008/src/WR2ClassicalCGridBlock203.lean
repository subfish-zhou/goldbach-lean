import WR2ClassicalCPayments
import WR2ClassicalCPoints203
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_203 (j : Fin 16) : cPayment (16*203+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*203+j.val)+point (1327/200) 4096 (16*203+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3248 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3248+point (1327/200) 4096 3249)/2)
    have hp : cPayment 3248 = (28068797772:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3248+point (1327/200) 4096 3249)/2 = (6700719:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3248
  · change cPayment 3249 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3249+point (1327/200) 4096 3250)/2)
    have hp : cPayment 3249 = (28034700383:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3249+point (1327/200) 4096 3250)/2 = (6701773:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3249
  · change cPayment 3250 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3250+point (1327/200) 4096 3251)/2)
    have hp : cPayment 3250 = (28000604184:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3250+point (1327/200) 4096 3251)/2 = (6702827:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3250
  · change cPayment 3251 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3251+point (1327/200) 4096 3252)/2)
    have hp : cPayment 3251 = (27966509182:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3251+point (1327/200) 4096 3252)/2 = (6703881:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3251
  · change cPayment 3252 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3252+point (1327/200) 4096 3253)/2)
    have hp : cPayment 3252 = (27932415382:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3252+point (1327/200) 4096 3253)/2 = (1340987:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3252
  · change cPayment 3253 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3253+point (1327/200) 4096 3254)/2)
    have hp : cPayment 3253 = (27898322788:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3253+point (1327/200) 4096 3254)/2 = (6705989:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3253
  · change cPayment 3254 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3254+point (1327/200) 4096 3255)/2)
    have hp : cPayment 3254 = (27864231407:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3254+point (1327/200) 4096 3255)/2 = (6707043:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3254
  · change cPayment 3255 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3255+point (1327/200) 4096 3256)/2)
    have hp : cPayment 3255 = (27830141243:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3255+point (1327/200) 4096 3256)/2 = (6708097:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3255
  · change cPayment 3256 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3256+point (1327/200) 4096 3257)/2)
    have hp : cPayment 3256 = (27796052301:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3256+point (1327/200) 4096 3257)/2 = (6709151:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3256
  · change cPayment 3257 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3257+point (1327/200) 4096 3258)/2)
    have hp : cPayment 3257 = (27761964587:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3257+point (1327/200) 4096 3258)/2 = (1342041:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3257
  · change cPayment 3258 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3258+point (1327/200) 4096 3259)/2)
    have hp : cPayment 3258 = (27727878106:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3258+point (1327/200) 4096 3259)/2 = (6711259:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3258
  · change cPayment 3259 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3259+point (1327/200) 4096 3260)/2)
    have hp : cPayment 3259 = (27693792863:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3259+point (1327/200) 4096 3260)/2 = (6712313:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3259
  · change cPayment 3260 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3260+point (1327/200) 4096 3261)/2)
    have hp : cPayment 3260 = (27659708862:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3260+point (1327/200) 4096 3261)/2 = (6713367:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3260
  · change cPayment 3261 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3261+point (1327/200) 4096 3262)/2)
    have hp : cPayment 3261 = (27625626111:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3261+point (1327/200) 4096 3262)/2 = (6714421:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3261
  · change cPayment 3262 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3262+point (1327/200) 4096 3263)/2)
    have hp : cPayment 3262 = (27591544612:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3262+point (1327/200) 4096 3263)/2 = (268619:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3262
  · change cPayment 3263 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3263+point (1327/200) 4096 3264)/2)
    have hp : cPayment 3263 = (27557464372:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3263+point (1327/200) 4096 3264)/2 = (6716529:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3263
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_203
