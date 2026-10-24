import WR2ClassicalCPayments
import WR2ClassicalCPoints016
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_016 (j : Fin 16) : cPayment (16*16+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*16+j.val)+point (1327/200) 4096 (16*16+j.val+1))/2) := by
  fin_cases j
  · change cPayment 256 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 256+point (1327/200) 4096 257)/2)
    have hp : cPayment 256 = (40692829366:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 256+point (1327/200) 4096 257)/2 = (3547151:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_256
  · change cPayment 257 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 257+point (1327/200) 4096 258)/2)
    have hp : cPayment 257 = (40813397960:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 257+point (1327/200) 4096 258)/2 = (709641:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_257
  · change cPayment 258 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 258+point (1327/200) 4096 259)/2)
    have hp : cPayment 258 = (40933713249:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 258+point (1327/200) 4096 259)/2 = (3549259:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_258
  · change cPayment 259 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 259+point (1327/200) 4096 260)/2)
    have hp : cPayment 259 = (41053775663:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 259+point (1327/200) 4096 260)/2 = (3550313:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_259
  · change cPayment 260 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 260+point (1327/200) 4096 261)/2)
    have hp : cPayment 260 = (41173585633:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 260+point (1327/200) 4096 261)/2 = (3551367:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_260
  · change cPayment 261 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 261+point (1327/200) 4096 262)/2)
    have hp : cPayment 261 = (41293143587:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 261+point (1327/200) 4096 262)/2 = (3552421:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_261
  · change cPayment 262 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 262+point (1327/200) 4096 263)/2)
    have hp : cPayment 262 = (41412449956:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 262+point (1327/200) 4096 263)/2 = (142139:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_262
  · change cPayment 263 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 263+point (1327/200) 4096 264)/2)
    have hp : cPayment 263 = (41531505165:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 263+point (1327/200) 4096 264)/2 = (3554529:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_263
  · change cPayment 264 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 264+point (1327/200) 4096 265)/2)
    have hp : cPayment 264 = (41650309643:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 264+point (1327/200) 4096 265)/2 = (3555583:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_264
  · change cPayment 265 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 265+point (1327/200) 4096 266)/2)
    have hp : cPayment 265 = (41768863814:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 265+point (1327/200) 4096 266)/2 = (3556637:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_265
  · change cPayment 266 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 266+point (1327/200) 4096 267)/2)
    have hp : cPayment 266 = (41887168104:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 266+point (1327/200) 4096 267)/2 = (3557691:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_266
  · change cPayment 267 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 267+point (1327/200) 4096 268)/2)
    have hp : cPayment 267 = (42005222937:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 267+point (1327/200) 4096 268)/2 = (711749:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_267
  · change cPayment 268 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 268+point (1327/200) 4096 269)/2)
    have hp : cPayment 268 = (42123028738:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 268+point (1327/200) 4096 269)/2 = (3559799:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_268
  · change cPayment 269 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 269+point (1327/200) 4096 270)/2)
    have hp : cPayment 269 = (42240585927:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 269+point (1327/200) 4096 270)/2 = (3560853:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_269
  · change cPayment 270 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 270+point (1327/200) 4096 271)/2)
    have hp : cPayment 270 = (42357894929:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 270+point (1327/200) 4096 271)/2 = (3561907:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_270
  · change cPayment 271 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 271+point (1327/200) 4096 272)/2)
    have hp : cPayment 271 = (42474956162:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 271+point (1327/200) 4096 272)/2 = (3562961:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_271
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_016
