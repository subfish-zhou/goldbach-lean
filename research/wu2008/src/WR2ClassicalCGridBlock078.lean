import WR2ClassicalCPayments
import WR2ClassicalCPoints078
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_078 (j : Fin 16) : cPayment (16*78+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*78+j.val)+point (1327/200) 4096 (16*78+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1248 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1248+point (1327/200) 4096 1249)/2)
    have hp : cPayment 1248 = (82687542666:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1248+point (1327/200) 4096 1249)/2 = (4592719:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1248
  · change cPayment 1249 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1249+point (1327/200) 4096 1250)/2)
    have hp : cPayment 1249 = (82683003573:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1249+point (1327/200) 4096 1250)/2 = (4593773:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1249
  · change cPayment 1250 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1250+point (1327/200) 4096 1251)/2)
    have hp : cPayment 1250 = (82678411742:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1250+point (1327/200) 4096 1251)/2 = (4594827:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1250
  · change cPayment 1251 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1251+point (1327/200) 4096 1252)/2)
    have hp : cPayment 1251 = (82673767253:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1251+point (1327/200) 4096 1252)/2 = (4595881:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1251
  · change cPayment 1252 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1252+point (1327/200) 4096 1253)/2)
    have hp : cPayment 1252 = (82669070187:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1252+point (1327/200) 4096 1253)/2 = (919387:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1252
  · change cPayment 1253 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1253+point (1327/200) 4096 1254)/2)
    have hp : cPayment 1253 = (82664320624:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1253+point (1327/200) 4096 1254)/2 = (4597989:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1253
  · change cPayment 1254 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1254+point (1327/200) 4096 1255)/2)
    have hp : cPayment 1254 = (82659518645:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1254+point (1327/200) 4096 1255)/2 = (4599043:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1254
  · change cPayment 1255 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1255+point (1327/200) 4096 1256)/2)
    have hp : cPayment 1255 = (82654664331:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1255+point (1327/200) 4096 1256)/2 = (4600097:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1255
  · change cPayment 1256 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1256+point (1327/200) 4096 1257)/2)
    have hp : cPayment 1256 = (82649757762:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1256+point (1327/200) 4096 1257)/2 = (4601151:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1256
  · change cPayment 1257 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1257+point (1327/200) 4096 1258)/2)
    have hp : cPayment 1257 = (82644799017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1257+point (1327/200) 4096 1258)/2 = (920441:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1257
  · change cPayment 1258 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1258+point (1327/200) 4096 1259)/2)
    have hp : cPayment 1258 = (82639788177:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1258+point (1327/200) 4096 1259)/2 = (4603259:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1258
  · change cPayment 1259 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1259+point (1327/200) 4096 1260)/2)
    have hp : cPayment 1259 = (82634725321:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1259+point (1327/200) 4096 1260)/2 = (4604313:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1259
  · change cPayment 1260 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1260+point (1327/200) 4096 1261)/2)
    have hp : cPayment 1260 = (82629610530:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1260+point (1327/200) 4096 1261)/2 = (4605367:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1260
  · change cPayment 1261 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1261+point (1327/200) 4096 1262)/2)
    have hp : cPayment 1261 = (82624443883:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1261+point (1327/200) 4096 1262)/2 = (4606421:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1261
  · change cPayment 1262 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1262+point (1327/200) 4096 1263)/2)
    have hp : cPayment 1262 = (82619225460:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1262+point (1327/200) 4096 1263)/2 = (184299:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1262
  · change cPayment 1263 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1263+point (1327/200) 4096 1264)/2)
    have hp : cPayment 1263 = (82613955340:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1263+point (1327/200) 4096 1264)/2 = (4608529:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1263
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_078
