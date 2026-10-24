import WR2ClassicalCPayments
import WR2ClassicalCPoints138
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_138 (j : Fin 16) : cPayment (16*138+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*138+j.val)+point (1327/200) 4096 (16*138+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2208 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2208+point (1327/200) 4096 2209)/2)
    have hp : cPayment 2208 = (62721499077:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2208+point (1327/200) 4096 2209)/2 = (5604559:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2208
  · change cPayment 2209 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2209+point (1327/200) 4096 2210)/2)
    have hp : cPayment 2209 = (62690942802:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2209+point (1327/200) 4096 2210)/2 = (5605613:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2209
  · change cPayment 2210 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2210+point (1327/200) 4096 2211)/2)
    have hp : cPayment 2210 = (62660375891:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2210+point (1327/200) 4096 2211)/2 = (5606667:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2210
  · change cPayment 2211 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2211+point (1327/200) 4096 2212)/2)
    have hp : cPayment 2211 = (62629798365:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2211+point (1327/200) 4096 2212)/2 = (5607721:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2211
  · change cPayment 2212 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2212+point (1327/200) 4096 2213)/2)
    have hp : cPayment 2212 = (62599210245:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2212+point (1327/200) 4096 2213)/2 = (224351:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2212
  · change cPayment 2213 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2213+point (1327/200) 4096 2214)/2)
    have hp : cPayment 2213 = (62568611553:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2213+point (1327/200) 4096 2214)/2 = (5609829:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2213
  · change cPayment 2214 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2214+point (1327/200) 4096 2215)/2)
    have hp : cPayment 2214 = (62538002309:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2214+point (1327/200) 4096 2215)/2 = (5610883:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2214
  · change cPayment 2215 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2215+point (1327/200) 4096 2216)/2)
    have hp : cPayment 2215 = (62507382534:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2215+point (1327/200) 4096 2216)/2 = (5611937:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2215
  · change cPayment 2216 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2216+point (1327/200) 4096 2217)/2)
    have hp : cPayment 2216 = (62476752248:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2216+point (1327/200) 4096 2217)/2 = (5612991:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2216
  · change cPayment 2217 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2217+point (1327/200) 4096 2218)/2)
    have hp : cPayment 2217 = (62446111474:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2217+point (1327/200) 4096 2218)/2 = (1122809:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2217
  · change cPayment 2218 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2218+point (1327/200) 4096 2219)/2)
    have hp : cPayment 2218 = (62415460230:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2218+point (1327/200) 4096 2219)/2 = (5615099:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2218
  · change cPayment 2219 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2219+point (1327/200) 4096 2220)/2)
    have hp : cPayment 2219 = (62384798539:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2219+point (1327/200) 4096 2220)/2 = (5616153:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2219
  · change cPayment 2220 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2220+point (1327/200) 4096 2221)/2)
    have hp : cPayment 2220 = (62354126421:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2220+point (1327/200) 4096 2221)/2 = (5617207:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2220
  · change cPayment 2221 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2221+point (1327/200) 4096 2222)/2)
    have hp : cPayment 2221 = (62323443897:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2221+point (1327/200) 4096 2222)/2 = (5618261:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2221
  · change cPayment 2222 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2222+point (1327/200) 4096 2223)/2)
    have hp : cPayment 2222 = (62292750987:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2222+point (1327/200) 4096 2223)/2 = (1123863:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2222
  · change cPayment 2223 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2223+point (1327/200) 4096 2224)/2)
    have hp : cPayment 2223 = (62262047712:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2223+point (1327/200) 4096 2224)/2 = (5620369:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2223
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_138
