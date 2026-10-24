import WR2ClassicalCPayments
import WR2ClassicalCPoints015
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_015 (j : Fin 16) : cPayment (16*15+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*15+j.val)+point (1327/200) 4096 (16*15+j.val+1))/2) := by
  fin_cases j
  · change cPayment 240 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 240+point (1327/200) 4096 241)/2)
    have hp : cPayment 240 = (38728927404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 240+point (1327/200) 4096 241)/2 = (3530287:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_240
  · change cPayment 241 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 241+point (1327/200) 4096 242)/2)
    have hp : cPayment 241 = (38853608184:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 241+point (1327/200) 4096 242)/2 = (3531341:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_241
  · change cPayment 242 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 242+point (1327/200) 4096 243)/2)
    have hp : cPayment 242 = (38978028648:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 242+point (1327/200) 4096 243)/2 = (706479:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_242
  · change cPayment 243 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 243+point (1327/200) 4096 244)/2)
    have hp : cPayment 243 = (39102189240:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 243+point (1327/200) 4096 244)/2 = (3533449:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_243
  · change cPayment 244 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 244+point (1327/200) 4096 245)/2)
    have hp : cPayment 244 = (39226090404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 244+point (1327/200) 4096 245)/2 = (3534503:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_244
  · change cPayment 245 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 245+point (1327/200) 4096 246)/2)
    have hp : cPayment 245 = (39349732584:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 245+point (1327/200) 4096 246)/2 = (3535557:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_245
  · change cPayment 246 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 246+point (1327/200) 4096 247)/2)
    have hp : cPayment 246 = (39473116221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 246+point (1327/200) 4096 247)/2 = (3536611:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_246
  · change cPayment 247 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 247+point (1327/200) 4096 248)/2)
    have hp : cPayment 247 = (39596241756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 247+point (1327/200) 4096 248)/2 = (707533:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_247
  · change cPayment 248 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 248+point (1327/200) 4096 249)/2)
    have hp : cPayment 248 = (39719109630:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 248+point (1327/200) 4096 249)/2 = (3538719:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_248
  · change cPayment 249 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 249+point (1327/200) 4096 250)/2)
    have hp : cPayment 249 = (39841720282:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 249+point (1327/200) 4096 250)/2 = (3539773:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_249
  · change cPayment 250 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 250+point (1327/200) 4096 251)/2)
    have hp : cPayment 250 = (39964074151:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 250+point (1327/200) 4096 251)/2 = (3540827:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_250
  · change cPayment 251 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 251+point (1327/200) 4096 252)/2)
    have hp : cPayment 251 = (40086171674:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 251+point (1327/200) 4096 252)/2 = (3541881:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_251
  · change cPayment 252 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 252+point (1327/200) 4096 253)/2)
    have hp : cPayment 252 = (40208013289:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 252+point (1327/200) 4096 253)/2 = (708587:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_252
  · change cPayment 253 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 253+point (1327/200) 4096 254)/2)
    have hp : cPayment 253 = (40329599430:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 253+point (1327/200) 4096 254)/2 = (3543989:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_253
  · change cPayment 254 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 254+point (1327/200) 4096 255)/2)
    have hp : cPayment 254 = (40450930534:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 254+point (1327/200) 4096 255)/2 = (3545043:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_254
  · change cPayment 255 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 255+point (1327/200) 4096 256)/2)
    have hp : cPayment 255 = (40572007035:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 255+point (1327/200) 4096 256)/2 = (3546097:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_255
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_015
