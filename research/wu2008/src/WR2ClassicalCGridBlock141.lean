import WR2ClassicalCPayments
import WR2ClassicalCPoints141
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_141 (j : Fin 16) : cPayment (16*141+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*141+j.val)+point (1327/200) 4096 (16*141+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2256 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2256+point (1327/200) 4096 2257)/2)
    have hp : cPayment 2256 = (61243158435:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2256+point (1327/200) 4096 2257)/2 = (5655151:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2256
  · change cPayment 2257 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2257+point (1327/200) 4096 2258)/2)
    have hp : cPayment 2257 = (61212114844:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2257+point (1327/200) 4096 2258)/2 = (1131241:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2257
  · change cPayment 2258 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2258+point (1327/200) 4096 2259)/2)
    have hp : cPayment 2258 = (61181061593:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2258+point (1327/200) 4096 2259)/2 = (5657259:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2258
  · change cPayment 2259 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2259+point (1327/200) 4096 2260)/2)
    have hp : cPayment 2259 = (61149998703:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2259+point (1327/200) 4096 2260)/2 = (5658313:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2259
  · change cPayment 2260 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2260+point (1327/200) 4096 2261)/2)
    have hp : cPayment 2260 = (61118926194:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2260+point (1327/200) 4096 2261)/2 = (5659367:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2260
  · change cPayment 2261 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2261+point (1327/200) 4096 2262)/2)
    have hp : cPayment 2261 = (61087844083:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2261+point (1327/200) 4096 2262)/2 = (5660421:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2261
  · change cPayment 2262 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2262+point (1327/200) 4096 2263)/2)
    have hp : cPayment 2262 = (61056752393:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2262+point (1327/200) 4096 2263)/2 = (226459:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2262
  · change cPayment 2263 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2263+point (1327/200) 4096 2264)/2)
    have hp : cPayment 2263 = (61025651141:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2263+point (1327/200) 4096 2264)/2 = (5662529:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2263
  · change cPayment 2264 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2264+point (1327/200) 4096 2265)/2)
    have hp : cPayment 2264 = (60994540347:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2264+point (1327/200) 4096 2265)/2 = (5663583:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2264
  · change cPayment 2265 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2265+point (1327/200) 4096 2266)/2)
    have hp : cPayment 2265 = (60963420032:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2265+point (1327/200) 4096 2266)/2 = (5664637:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2265
  · change cPayment 2266 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2266+point (1327/200) 4096 2267)/2)
    have hp : cPayment 2266 = (60932290214:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2266+point (1327/200) 4096 2267)/2 = (5665691:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2266
  · change cPayment 2267 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2267+point (1327/200) 4096 2268)/2)
    have hp : cPayment 2267 = (60901150913:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2267+point (1327/200) 4096 2268)/2 = (1133349:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2267
  · change cPayment 2268 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2268+point (1327/200) 4096 2269)/2)
    have hp : cPayment 2268 = (60870002149:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2268+point (1327/200) 4096 2269)/2 = (5667799:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2268
  · change cPayment 2269 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2269+point (1327/200) 4096 2270)/2)
    have hp : cPayment 2269 = (60838843940:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2269+point (1327/200) 4096 2270)/2 = (5668853:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2269
  · change cPayment 2270 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2270+point (1327/200) 4096 2271)/2)
    have hp : cPayment 2270 = (60807676306:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2270+point (1327/200) 4096 2271)/2 = (5669907:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2270
  · change cPayment 2271 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2271+point (1327/200) 4096 2272)/2)
    have hp : cPayment 2271 = (60776499268:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2271+point (1327/200) 4096 2272)/2 = (5670961:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2271
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_141
