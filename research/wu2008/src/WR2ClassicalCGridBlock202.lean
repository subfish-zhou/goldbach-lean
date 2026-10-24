import WR2ClassicalCPayments
import WR2ClassicalCPoints202
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_202 (j : Fin 16) : cPayment (16*202+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*202+j.val)+point (1327/200) 4096 (16*202+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3232 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3232+point (1327/200) 4096 3233)/2)
    have hp : cPayment 3232 = (28614513722:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3232+point (1327/200) 4096 3233)/2 = (1336771:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3232
  · change cPayment 3233 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3233+point (1327/200) 4096 3234)/2)
    have hp : cPayment 3233 = (28580397989:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3233+point (1327/200) 4096 3234)/2 = (6684909:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3233
  · change cPayment 3234 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3234+point (1327/200) 4096 3235)/2)
    have hp : cPayment 3234 = (28546283363:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3234+point (1327/200) 4096 3235)/2 = (6685963:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3234
  · change cPayment 3235 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3235+point (1327/200) 4096 3236)/2)
    have hp : cPayment 3235 = (28512169849:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3235+point (1327/200) 4096 3236)/2 = (6687017:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3235
  · change cPayment 3236 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3236+point (1327/200) 4096 3237)/2)
    have hp : cPayment 3236 = (28478057452:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3236+point (1327/200) 4096 3237)/2 = (6688071:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3236
  · change cPayment 3237 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3237+point (1327/200) 4096 3238)/2)
    have hp : cPayment 3237 = (28443946178:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3237+point (1327/200) 4096 3238)/2 = (267565:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3237
  · change cPayment 3238 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3238+point (1327/200) 4096 3239)/2)
    have hp : cPayment 3238 = (28409836032:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3238+point (1327/200) 4096 3239)/2 = (6690179:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3238
  · change cPayment 3239 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3239+point (1327/200) 4096 3240)/2)
    have hp : cPayment 3239 = (28375727019:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3239+point (1327/200) 4096 3240)/2 = (6691233:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3239
  · change cPayment 3240 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3240+point (1327/200) 4096 3241)/2)
    have hp : cPayment 3240 = (28341619144:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3240+point (1327/200) 4096 3241)/2 = (6692287:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3240
  · change cPayment 3241 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3241+point (1327/200) 4096 3242)/2)
    have hp : cPayment 3241 = (28307512414:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3241+point (1327/200) 4096 3242)/2 = (6693341:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3241
  · change cPayment 3242 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3242+point (1327/200) 4096 3243)/2)
    have hp : cPayment 3242 = (28273406833:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3242+point (1327/200) 4096 3243)/2 = (1338879:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3242
  · change cPayment 3243 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3243+point (1327/200) 4096 3244)/2)
    have hp : cPayment 3243 = (28239302406:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3243+point (1327/200) 4096 3244)/2 = (6695449:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3243
  · change cPayment 3244 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3244+point (1327/200) 4096 3245)/2)
    have hp : cPayment 3244 = (28205199139:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3244+point (1327/200) 4096 3245)/2 = (6696503:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3244
  · change cPayment 3245 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3245+point (1327/200) 4096 3246)/2)
    have hp : cPayment 3245 = (28171097036:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3245+point (1327/200) 4096 3246)/2 = (6697557:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3245
  · change cPayment 3246 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3246+point (1327/200) 4096 3247)/2)
    have hp : cPayment 3246 = (28136996104:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3246+point (1327/200) 4096 3247)/2 = (6698611:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3246
  · change cPayment 3247 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3247+point (1327/200) 4096 3248)/2)
    have hp : cPayment 3247 = (28102896348:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3247+point (1327/200) 4096 3248)/2 = (1339933:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3247
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_202
