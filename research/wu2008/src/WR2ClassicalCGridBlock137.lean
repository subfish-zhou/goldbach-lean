import WR2ClassicalCPayments
import WR2ClassicalCPoints137
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_137 (j : Fin 16) : cPayment (16*137+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*137+j.val)+point (1327/200) 4096 (16*137+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2192 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2192+point (1327/200) 4096 2193)/2)
    have hp : cPayment 2192 = (63208935797:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2192+point (1327/200) 4096 2193)/2 = (1117539:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2192
  · change cPayment 2193 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2193+point (1327/200) 4096 2194)/2)
    have hp : cPayment 2193 = (63178552569:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2193+point (1327/200) 4096 2194)/2 = (5588749:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2193
  · change cPayment 2194 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2194+point (1327/200) 4096 2195)/2)
    have hp : cPayment 2194 = (63148158367:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2194+point (1327/200) 4096 2195)/2 = (5589803:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2194
  · change cPayment 2195 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2195+point (1327/200) 4096 2196)/2)
    have hp : cPayment 2195 = (63117753210:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2195+point (1327/200) 4096 2196)/2 = (5590857:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2195
  · change cPayment 2196 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2196+point (1327/200) 4096 2197)/2)
    have hp : cPayment 2196 = (63087337122:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2196+point (1327/200) 4096 2197)/2 = (5591911:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2196
  · change cPayment 2197 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2197+point (1327/200) 4096 2198)/2)
    have hp : cPayment 2197 = (63056910122:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2197+point (1327/200) 4096 2198)/2 = (1118593:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2197
  · change cPayment 2198 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2198+point (1327/200) 4096 2199)/2)
    have hp : cPayment 2198 = (63026472232:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2198+point (1327/200) 4096 2199)/2 = (5594019:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2198
  · change cPayment 2199 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2199+point (1327/200) 4096 2200)/2)
    have hp : cPayment 2199 = (62996023474:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2199+point (1327/200) 4096 2200)/2 = (5595073:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2199
  · change cPayment 2200 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2200+point (1327/200) 4096 2201)/2)
    have hp : cPayment 2200 = (62965563869:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2200+point (1327/200) 4096 2201)/2 = (5596127:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2200
  · change cPayment 2201 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2201+point (1327/200) 4096 2202)/2)
    have hp : cPayment 2201 = (62935093437:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2201+point (1327/200) 4096 2202)/2 = (5597181:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2201
  · change cPayment 2202 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2202+point (1327/200) 4096 2203)/2)
    have hp : cPayment 2202 = (62904612202:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2202+point (1327/200) 4096 2203)/2 = (1119647:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2202
  · change cPayment 2203 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2203+point (1327/200) 4096 2204)/2)
    have hp : cPayment 2203 = (62874120183:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2203+point (1327/200) 4096 2204)/2 = (5599289:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2203
  · change cPayment 2204 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2204+point (1327/200) 4096 2205)/2)
    have hp : cPayment 2204 = (62843617401:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2204+point (1327/200) 4096 2205)/2 = (5600343:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2204
  · change cPayment 2205 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2205+point (1327/200) 4096 2206)/2)
    have hp : cPayment 2205 = (62813103879:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2205+point (1327/200) 4096 2206)/2 = (5601397:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2205
  · change cPayment 2206 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2206+point (1327/200) 4096 2207)/2)
    have hp : cPayment 2206 = (62782579637:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2206+point (1327/200) 4096 2207)/2 = (5602451:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2206
  · change cPayment 2207 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2207+point (1327/200) 4096 2208)/2)
    have hp : cPayment 2207 = (62752044696:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2207+point (1327/200) 4096 2208)/2 = (1120701:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2207
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_137
