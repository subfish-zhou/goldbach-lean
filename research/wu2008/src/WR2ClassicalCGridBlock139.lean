import WR2ClassicalCPayments
import WR2ClassicalCPoints139
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_139 (j : Fin 16) : cPayment (16*139+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*139+j.val)+point (1327/200) 4096 (16*139+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2224 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2224+point (1327/200) 4096 2225)/2)
    have hp : cPayment 2224 = (62231334092:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2224+point (1327/200) 4096 2225)/2 = (5621423:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2224
  · change cPayment 2225 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2225+point (1327/200) 4096 2226)/2)
    have hp : cPayment 2225 = (62200610149:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2225+point (1327/200) 4096 2226)/2 = (5622477:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2225
  · change cPayment 2226 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2226+point (1327/200) 4096 2227)/2)
    have hp : cPayment 2226 = (62169875902:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2226+point (1327/200) 4096 2227)/2 = (5623531:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2226
  · change cPayment 2227 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2227+point (1327/200) 4096 2228)/2)
    have hp : cPayment 2227 = (62139131373:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2227+point (1327/200) 4096 2228)/2 = (1124917:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2227
  · change cPayment 2228 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2228+point (1327/200) 4096 2229)/2)
    have hp : cPayment 2228 = (62108376582:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2228+point (1327/200) 4096 2229)/2 = (5625639:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2228
  · change cPayment 2229 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2229+point (1327/200) 4096 2230)/2)
    have hp : cPayment 2229 = (62077611549:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2229+point (1327/200) 4096 2230)/2 = (5626693:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2229
  · change cPayment 2230 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2230+point (1327/200) 4096 2231)/2)
    have hp : cPayment 2230 = (62046836295:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2230+point (1327/200) 4096 2231)/2 = (5627747:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2230
  · change cPayment 2231 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2231+point (1327/200) 4096 2232)/2)
    have hp : cPayment 2231 = (62016050840:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2231+point (1327/200) 4096 2232)/2 = (5628801:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2231
  · change cPayment 2232 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2232+point (1327/200) 4096 2233)/2)
    have hp : cPayment 2232 = (61985255205:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2232+point (1327/200) 4096 2233)/2 = (1125971:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2232
  · change cPayment 2233 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2233+point (1327/200) 4096 2234)/2)
    have hp : cPayment 2233 = (61954449410:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2233+point (1327/200) 4096 2234)/2 = (5630909:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2233
  · change cPayment 2234 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2234+point (1327/200) 4096 2235)/2)
    have hp : cPayment 2234 = (61923633475:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2234+point (1327/200) 4096 2235)/2 = (5631963:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2234
  · change cPayment 2235 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2235+point (1327/200) 4096 2236)/2)
    have hp : cPayment 2235 = (61892807421:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2235+point (1327/200) 4096 2236)/2 = (5633017:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2235
  · change cPayment 2236 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2236+point (1327/200) 4096 2237)/2)
    have hp : cPayment 2236 = (61861971268:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2236+point (1327/200) 4096 2237)/2 = (5634071:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2236
  · change cPayment 2237 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2237+point (1327/200) 4096 2238)/2)
    have hp : cPayment 2237 = (61831125036:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2237+point (1327/200) 4096 2238)/2 = (225405:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2237
  · change cPayment 2238 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2238+point (1327/200) 4096 2239)/2)
    have hp : cPayment 2238 = (61800268746:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2238+point (1327/200) 4096 2239)/2 = (5636179:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2238
  · change cPayment 2239 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2239+point (1327/200) 4096 2240)/2)
    have hp : cPayment 2239 = (61769402417:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2239+point (1327/200) 4096 2240)/2 = (5637233:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2239
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_139
