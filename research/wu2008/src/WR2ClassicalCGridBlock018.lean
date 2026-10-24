import WR2ClassicalCPayments
import WR2ClassicalCPoints018
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_018 (j : Fin 16) : cPayment (16*18+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*18+j.val)+point (1327/200) 4096 (16*18+j.val+1))/2) := by
  fin_cases j
  · change cPayment 288 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 288+point (1327/200) 4096 289)/2)
    have hp : cPayment 288 = (44427492774:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 288+point (1327/200) 4096 289)/2 = (3580879:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_288
  · change cPayment 289 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 289+point (1327/200) 4096 290)/2)
    have hp : cPayment 289 = (44540165272:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 289+point (1327/200) 4096 290)/2 = (3581933:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_289
  · change cPayment 290 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 290+point (1327/200) 4096 291)/2)
    have hp : cPayment 290 = (44652597850:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 290+point (1327/200) 4096 291)/2 = (3582987:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_290
  · change cPayment 291 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 291+point (1327/200) 4096 292)/2)
    have hp : cPayment 291 = (44764790912:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 291+point (1327/200) 4096 292)/2 = (3584041:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_291
  · change cPayment 292 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 292+point (1327/200) 4096 293)/2)
    have hp : cPayment 292 = (44876744864:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 292+point (1327/200) 4096 293)/2 = (717019:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_292
  · change cPayment 293 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 293+point (1327/200) 4096 294)/2)
    have hp : cPayment 293 = (44988460109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 293+point (1327/200) 4096 294)/2 = (3586149:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_293
  · change cPayment 294 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 294+point (1327/200) 4096 295)/2)
    have hp : cPayment 294 = (45099937049:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 294+point (1327/200) 4096 295)/2 = (3587203:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_294
  · change cPayment 295 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 295+point (1327/200) 4096 296)/2)
    have hp : cPayment 295 = (45211176088:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 295+point (1327/200) 4096 296)/2 = (3588257:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_295
  · change cPayment 296 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 296+point (1327/200) 4096 297)/2)
    have hp : cPayment 296 = (45322177625:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 296+point (1327/200) 4096 297)/2 = (3589311:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_296
  · change cPayment 297 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 297+point (1327/200) 4096 298)/2)
    have hp : cPayment 297 = (45432942062:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 297+point (1327/200) 4096 298)/2 = (718073:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_297
  · change cPayment 298 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 298+point (1327/200) 4096 299)/2)
    have hp : cPayment 298 = (45543469797:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 298+point (1327/200) 4096 299)/2 = (3591419:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_298
  · change cPayment 299 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 299+point (1327/200) 4096 300)/2)
    have hp : cPayment 299 = (45653761231:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 299+point (1327/200) 4096 300)/2 = (3592473:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_299
  · change cPayment 300 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 300+point (1327/200) 4096 301)/2)
    have hp : cPayment 300 = (45763816762:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 300+point (1327/200) 4096 301)/2 = (3593527:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_300
  · change cPayment 301 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 301+point (1327/200) 4096 302)/2)
    have hp : cPayment 301 = (45873636786:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 301+point (1327/200) 4096 302)/2 = (3594581:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_301
  · change cPayment 302 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 302+point (1327/200) 4096 303)/2)
    have hp : cPayment 302 = (45983221701:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 302+point (1327/200) 4096 303)/2 = (719127:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_302
  · change cPayment 303 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 303+point (1327/200) 4096 304)/2)
    have hp : cPayment 303 = (46092571902:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 303+point (1327/200) 4096 304)/2 = (3596689:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_303
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_018
