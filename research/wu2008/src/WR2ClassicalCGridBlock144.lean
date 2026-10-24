import WR2ClassicalCPayments
import WR2ClassicalCPoints144
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_144 (j : Fin 16) : cPayment (16*144+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*144+j.val)+point (1327/200) 4096 (16*144+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2304 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2304+point (1327/200) 4096 2305)/2)
    have hp : cPayment 2304 = (59742505819:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2304+point (1327/200) 4096 2305)/2 = (5705743:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2304
  · change cPayment 2305 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2305+point (1327/200) 4096 2306)/2)
    have hp : cPayment 2305 = (59711020340:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2305+point (1327/200) 4096 2306)/2 = (5706797:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2305
  · change cPayment 2306 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2306+point (1327/200) 4096 2307)/2)
    have hp : cPayment 2306 = (59679526116:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2306+point (1327/200) 4096 2307)/2 = (5707851:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2306
  · change cPayment 2307 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2307+point (1327/200) 4096 2308)/2)
    have hp : cPayment 2307 = (59648023168:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2307+point (1327/200) 4096 2308)/2 = (1141781:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2307
  · change cPayment 2308 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2308+point (1327/200) 4096 2309)/2)
    have hp : cPayment 2308 = (59616511513:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2308+point (1327/200) 4096 2309)/2 = (5709959:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2308
  · change cPayment 2309 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2309+point (1327/200) 4096 2310)/2)
    have hp : cPayment 2309 = (59584991170:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2309+point (1327/200) 4096 2310)/2 = (5711013:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2309
  · change cPayment 2310 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2310+point (1327/200) 4096 2311)/2)
    have hp : cPayment 2310 = (59553462157:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2310+point (1327/200) 4096 2311)/2 = (5712067:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2310
  · change cPayment 2311 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2311+point (1327/200) 4096 2312)/2)
    have hp : cPayment 2311 = (59521924492:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2311+point (1327/200) 4096 2312)/2 = (5713121:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2311
  · change cPayment 2312 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2312+point (1327/200) 4096 2313)/2)
    have hp : cPayment 2312 = (59490378195:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2312+point (1327/200) 4096 2313)/2 = (228567:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2312
  · change cPayment 2313 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2313+point (1327/200) 4096 2314)/2)
    have hp : cPayment 2313 = (59458823283:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2313+point (1327/200) 4096 2314)/2 = (5715229:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2313
  · change cPayment 2314 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2314+point (1327/200) 4096 2315)/2)
    have hp : cPayment 2314 = (59427259774:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2314+point (1327/200) 4096 2315)/2 = (5716283:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2314
  · change cPayment 2315 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2315+point (1327/200) 4096 2316)/2)
    have hp : cPayment 2315 = (59395687687:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2315+point (1327/200) 4096 2316)/2 = (5717337:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2315
  · change cPayment 2316 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2316+point (1327/200) 4096 2317)/2)
    have hp : cPayment 2316 = (59364107040:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2316+point (1327/200) 4096 2317)/2 = (5718391:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2316
  · change cPayment 2317 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2317+point (1327/200) 4096 2318)/2)
    have hp : cPayment 2317 = (59332517852:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2317+point (1327/200) 4096 2318)/2 = (1143889:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2317
  · change cPayment 2318 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2318+point (1327/200) 4096 2319)/2)
    have hp : cPayment 2318 = (59300920140:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2318+point (1327/200) 4096 2319)/2 = (5720499:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2318
  · change cPayment 2319 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2319+point (1327/200) 4096 2320)/2)
    have hp : cPayment 2319 = (59269313922:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2319+point (1327/200) 4096 2320)/2 = (5721553:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2319
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_144
