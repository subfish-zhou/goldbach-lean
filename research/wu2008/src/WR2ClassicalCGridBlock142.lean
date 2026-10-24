import WR2ClassicalCPayments
import WR2ClassicalCPoints142
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_142 (j : Fin 16) : cPayment (16*142+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*142+j.val)+point (1327/200) 4096 (16*142+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2272 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2272+point (1327/200) 4096 2273)/2)
    have hp : cPayment 2272 = (60745312843:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2272+point (1327/200) 4096 2273)/2 = (1134403:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2272
  · change cPayment 2273 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2273+point (1327/200) 4096 2274)/2)
    have hp : cPayment 2273 = (60714117051:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2273+point (1327/200) 4096 2274)/2 = (5673069:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2273
  · change cPayment 2274 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2274+point (1327/200) 4096 2275)/2)
    have hp : cPayment 2274 = (60682911912:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2274+point (1327/200) 4096 2275)/2 = (5674123:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2274
  · change cPayment 2275 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2275+point (1327/200) 4096 2276)/2)
    have hp : cPayment 2275 = (60651697444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2275+point (1327/200) 4096 2276)/2 = (5675177:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2275
  · change cPayment 2276 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2276+point (1327/200) 4096 2277)/2)
    have hp : cPayment 2276 = (60620473668:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2276+point (1327/200) 4096 2277)/2 = (5676231:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2276
  · change cPayment 2277 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2277+point (1327/200) 4096 2278)/2)
    have hp : cPayment 2277 = (60589240602:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2277+point (1327/200) 4096 2278)/2 = (1135457:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2277
  · change cPayment 2278 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2278+point (1327/200) 4096 2279)/2)
    have hp : cPayment 2278 = (60557998265:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2278+point (1327/200) 4096 2279)/2 = (5678339:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2278
  · change cPayment 2279 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2279+point (1327/200) 4096 2280)/2)
    have hp : cPayment 2279 = (60526746678:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2279+point (1327/200) 4096 2280)/2 = (5679393:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2279
  · change cPayment 2280 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2280+point (1327/200) 4096 2281)/2)
    have hp : cPayment 2280 = (60495485857:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2280+point (1327/200) 4096 2281)/2 = (5680447:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2280
  · change cPayment 2281 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2281+point (1327/200) 4096 2282)/2)
    have hp : cPayment 2281 = (60464215824:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2281+point (1327/200) 4096 2282)/2 = (5681501:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2281
  · change cPayment 2282 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2282+point (1327/200) 4096 2283)/2)
    have hp : cPayment 2282 = (60432936597:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2282+point (1327/200) 4096 2283)/2 = (1136511:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2282
  · change cPayment 2283 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2283+point (1327/200) 4096 2284)/2)
    have hp : cPayment 2283 = (60401648194:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2283+point (1327/200) 4096 2284)/2 = (5683609:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2283
  · change cPayment 2284 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2284+point (1327/200) 4096 2285)/2)
    have hp : cPayment 2284 = (60370350636:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2284+point (1327/200) 4096 2285)/2 = (5684663:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2284
  · change cPayment 2285 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2285+point (1327/200) 4096 2286)/2)
    have hp : cPayment 2285 = (60339043941:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2285+point (1327/200) 4096 2286)/2 = (5685717:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2285
  · change cPayment 2286 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2286+point (1327/200) 4096 2287)/2)
    have hp : cPayment 2286 = (60307728128:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2286+point (1327/200) 4096 2287)/2 = (5686771:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2286
  · change cPayment 2287 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2287+point (1327/200) 4096 2288)/2)
    have hp : cPayment 2287 = (60276403216:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2287+point (1327/200) 4096 2288)/2 = (227513:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2287
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_142
