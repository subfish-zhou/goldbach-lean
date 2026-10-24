import WR2ClassicalCPayments
import WR2ClassicalCPoints012
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_012 (j : Fin 16) : cPayment (16*12+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*12+j.val)+point (1327/200) 4096 (16*12+j.val+1))/2) := by
  fin_cases j
  · change cPayment 192 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 192+point (1327/200) 4096 193)/2)
    have hp : cPayment 192 = (32429181939:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 192+point (1327/200) 4096 193)/2 = (695939:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_192
  · change cPayment 193 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 193+point (1327/200) 4096 194)/2)
    have hp : cPayment 193 = (32566898266:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 193+point (1327/200) 4096 194)/2 = (3480749:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_193
  · change cPayment 194 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 194+point (1327/200) 4096 195)/2)
    have hp : cPayment 194 = (32704331874:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 194+point (1327/200) 4096 195)/2 = (3481803:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_194
  · change cPayment 195 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 195+point (1327/200) 4096 196)/2)
    have hp : cPayment 195 = (32841483253:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 195+point (1327/200) 4096 196)/2 = (3482857:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_195
  · change cPayment 196 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 196+point (1327/200) 4096 197)/2)
    have hp : cPayment 196 = (32978352890:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 196+point (1327/200) 4096 197)/2 = (3483911:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_196
  · change cPayment 197 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 197+point (1327/200) 4096 198)/2)
    have hp : cPayment 197 = (33114941272:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 197+point (1327/200) 4096 198)/2 = (696993:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_197
  · change cPayment 198 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 198+point (1327/200) 4096 199)/2)
    have hp : cPayment 198 = (33251248885:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 198+point (1327/200) 4096 199)/2 = (3486019:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_198
  · change cPayment 199 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 199+point (1327/200) 4096 200)/2)
    have hp : cPayment 199 = (33387276214:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 199+point (1327/200) 4096 200)/2 = (3487073:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_199
  · change cPayment 200 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 200+point (1327/200) 4096 201)/2)
    have hp : cPayment 200 = (33523023742:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 200+point (1327/200) 4096 201)/2 = (3488127:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_200
  · change cPayment 201 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 201+point (1327/200) 4096 202)/2)
    have hp : cPayment 201 = (33658491952:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 201+point (1327/200) 4096 202)/2 = (3489181:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_201
  · change cPayment 202 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 202+point (1327/200) 4096 203)/2)
    have hp : cPayment 202 = (33793681327:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 202+point (1327/200) 4096 203)/2 = (698047:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_202
  · change cPayment 203 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 203+point (1327/200) 4096 204)/2)
    have hp : cPayment 203 = (33928592348:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 203+point (1327/200) 4096 204)/2 = (3491289:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_203
  · change cPayment 204 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 204+point (1327/200) 4096 205)/2)
    have hp : cPayment 204 = (34063225494:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 204+point (1327/200) 4096 205)/2 = (3492343:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_204
  · change cPayment 205 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 205+point (1327/200) 4096 206)/2)
    have hp : cPayment 205 = (34197581245:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 205+point (1327/200) 4096 206)/2 = (3493397:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_205
  · change cPayment 206 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 206+point (1327/200) 4096 207)/2)
    have hp : cPayment 206 = (34331660078:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 206+point (1327/200) 4096 207)/2 = (3494451:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_206
  · change cPayment 207 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 207+point (1327/200) 4096 208)/2)
    have hp : cPayment 207 = (34465462472:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 207+point (1327/200) 4096 208)/2 = (699101:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_207
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_012
