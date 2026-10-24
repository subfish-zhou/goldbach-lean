import WR2ClassicalCPayments
import WR2ClassicalCPoints140
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_140 (j : Fin 16) : cPayment (16*140+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*140+j.val)+point (1327/200) 4096 (16*140+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2240 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2240+point (1327/200) 4096 2241)/2)
    have hp : cPayment 2240 = (61738526070:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2240+point (1327/200) 4096 2241)/2 = (5638287:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2240
  · change cPayment 2241 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2241+point (1327/200) 4096 2242)/2)
    have hp : cPayment 2241 = (61707639726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2241+point (1327/200) 4096 2242)/2 = (5639341:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2241
  · change cPayment 2242 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2242+point (1327/200) 4096 2243)/2)
    have hp : cPayment 2242 = (61676743403:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2242+point (1327/200) 4096 2243)/2 = (1128079:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2242
  · change cPayment 2243 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2243+point (1327/200) 4096 2244)/2)
    have hp : cPayment 2243 = (61645837123:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2243+point (1327/200) 4096 2244)/2 = (5641449:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2243
  · change cPayment 2244 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2244+point (1327/200) 4096 2245)/2)
    have hp : cPayment 2244 = (61614920905:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2244+point (1327/200) 4096 2245)/2 = (5642503:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2244
  · change cPayment 2245 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2245+point (1327/200) 4096 2246)/2)
    have hp : cPayment 2245 = (61583994770:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2245+point (1327/200) 4096 2246)/2 = (5643557:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2245
  · change cPayment 2246 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2246+point (1327/200) 4096 2247)/2)
    have hp : cPayment 2246 = (61553058738:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2246+point (1327/200) 4096 2247)/2 = (5644611:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2246
  · change cPayment 2247 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2247+point (1327/200) 4096 2248)/2)
    have hp : cPayment 2247 = (61522112827:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2247+point (1327/200) 4096 2248)/2 = (1129133:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2247
  · change cPayment 2248 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2248+point (1327/200) 4096 2249)/2)
    have hp : cPayment 2248 = (61491157060:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2248+point (1327/200) 4096 2249)/2 = (5646719:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2248
  · change cPayment 2249 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2249+point (1327/200) 4096 2250)/2)
    have hp : cPayment 2249 = (61460191454:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2249+point (1327/200) 4096 2250)/2 = (5647773:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2249
  · change cPayment 2250 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2250+point (1327/200) 4096 2251)/2)
    have hp : cPayment 2250 = (61429216031:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2250+point (1327/200) 4096 2251)/2 = (5648827:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2250
  · change cPayment 2251 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2251+point (1327/200) 4096 2252)/2)
    have hp : cPayment 2251 = (61398230811:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2251+point (1327/200) 4096 2252)/2 = (5649881:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2251
  · change cPayment 2252 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2252+point (1327/200) 4096 2253)/2)
    have hp : cPayment 2252 = (61367235812:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2252+point (1327/200) 4096 2253)/2 = (1130187:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2252
  · change cPayment 2253 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2253+point (1327/200) 4096 2254)/2)
    have hp : cPayment 2253 = (61336231055:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2253+point (1327/200) 4096 2254)/2 = (5651989:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2253
  · change cPayment 2254 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2254+point (1327/200) 4096 2255)/2)
    have hp : cPayment 2254 = (61305216560:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2254+point (1327/200) 4096 2255)/2 = (5653043:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2254
  · change cPayment 2255 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2255+point (1327/200) 4096 2256)/2)
    have hp : cPayment 2255 = (61274192347:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2255+point (1327/200) 4096 2256)/2 = (5654097:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2255
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_140
