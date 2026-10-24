import WR2ClassicalCPayments
import WR2ClassicalCPoints014
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_014 (j : Fin 16) : cPayment (16*14+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*14+j.val)+point (1327/200) 4096 (16*14+j.val+1))/2) := by
  fin_cases j
  · change cPayment 224 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 224+point (1327/200) 4096 225)/2)
    have hp : cPayment 224 = (36698265766:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 224+point (1327/200) 4096 225)/2 = (3513423:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_224
  · change cPayment 225 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 225+point (1327/200) 4096 226)/2)
    have hp : cPayment 225 = (36827172784:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 225+point (1327/200) 4096 226)/2 = (3514477:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_225
  · change cPayment 226 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 226+point (1327/200) 4096 227)/2)
    have hp : cPayment 226 = (36955812252:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 226+point (1327/200) 4096 227)/2 = (3515531:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_226
  · change cPayment 227 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 227+point (1327/200) 4096 228)/2)
    have hp : cPayment 227 = (37084184629:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 227+point (1327/200) 4096 228)/2 = (703317:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_227
  · change cPayment 228 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 228+point (1327/200) 4096 229)/2)
    have hp : cPayment 228 = (37212290374:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 228+point (1327/200) 4096 229)/2 = (3517639:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_228
  · change cPayment 229 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 229+point (1327/200) 4096 230)/2)
    have hp : cPayment 229 = (37340129943:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 229+point (1327/200) 4096 230)/2 = (3518693:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_229
  · change cPayment 230 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 230+point (1327/200) 4096 231)/2)
    have hp : cPayment 230 = (37467703792:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 230+point (1327/200) 4096 231)/2 = (3519747:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_230
  · change cPayment 231 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 231+point (1327/200) 4096 232)/2)
    have hp : cPayment 231 = (37595012377:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 231+point (1327/200) 4096 232)/2 = (3520801:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_231
  · change cPayment 232 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 232+point (1327/200) 4096 233)/2)
    have hp : cPayment 232 = (37722056152:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 232+point (1327/200) 4096 233)/2 = (704371:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_232
  · change cPayment 233 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 233+point (1327/200) 4096 234)/2)
    have hp : cPayment 233 = (37848835570:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 233+point (1327/200) 4096 234)/2 = (3522909:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_233
  · change cPayment 234 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 234+point (1327/200) 4096 235)/2)
    have hp : cPayment 234 = (37975351084:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 234+point (1327/200) 4096 235)/2 = (3523963:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_234
  · change cPayment 235 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 235+point (1327/200) 4096 236)/2)
    have hp : cPayment 235 = (38101603145:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 235+point (1327/200) 4096 236)/2 = (3525017:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_235
  · change cPayment 236 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 236+point (1327/200) 4096 237)/2)
    have hp : cPayment 236 = (38227592204:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 236+point (1327/200) 4096 237)/2 = (3526071:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_236
  · change cPayment 237 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 237+point (1327/200) 4096 238)/2)
    have hp : cPayment 237 = (38353318711:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 237+point (1327/200) 4096 238)/2 = (141085:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_237
  · change cPayment 238 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 238+point (1327/200) 4096 239)/2)
    have hp : cPayment 238 = (38478783115:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 238+point (1327/200) 4096 239)/2 = (3528179:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_238
  · change cPayment 239 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 239+point (1327/200) 4096 240)/2)
    have hp : cPayment 239 = (38603985863:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 239+point (1327/200) 4096 240)/2 = (3529233:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_239
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_014
