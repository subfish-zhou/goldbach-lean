import WR2ClassicalCPayments
import WR2ClassicalCPoints136
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_136 (j : Fin 16) : cPayment (16*136+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*136+j.val)+point (1327/200) 4096 (16*136+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2176 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2176+point (1327/200) 4096 2177)/2)
    have hp : cPayment 2176 = (63693557174:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2176+point (1327/200) 4096 2177)/2 = (5570831:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2176
  · change cPayment 2177 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2177+point (1327/200) 4096 2178)/2)
    have hp : cPayment 2177 = (63663352493:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2177+point (1327/200) 4096 2178)/2 = (1114377:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2177
  · change cPayment 2178 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2178+point (1327/200) 4096 2179)/2)
    have hp : cPayment 2178 = (63633136489:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2178+point (1327/200) 4096 2179)/2 = (5572939:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2178
  · change cPayment 2179 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2179+point (1327/200) 4096 2180)/2)
    have hp : cPayment 2179 = (63602909184:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2179+point (1327/200) 4096 2180)/2 = (5573993:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2179
  · change cPayment 2180 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2180+point (1327/200) 4096 2181)/2)
    have hp : cPayment 2180 = (63572670601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2180+point (1327/200) 4096 2181)/2 = (5575047:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2180
  · change cPayment 2181 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2181+point (1327/200) 4096 2182)/2)
    have hp : cPayment 2181 = (63542420761:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2181+point (1327/200) 4096 2182)/2 = (5576101:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2181
  · change cPayment 2182 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2182+point (1327/200) 4096 2183)/2)
    have hp : cPayment 2182 = (63512159686:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2182+point (1327/200) 4096 2183)/2 = (1115431:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2182
  · change cPayment 2183 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2183+point (1327/200) 4096 2184)/2)
    have hp : cPayment 2183 = (63481887398:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2183+point (1327/200) 4096 2184)/2 = (5578209:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2183
  · change cPayment 2184 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2184+point (1327/200) 4096 2185)/2)
    have hp : cPayment 2184 = (63451603919:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2184+point (1327/200) 4096 2185)/2 = (5579263:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2184
  · change cPayment 2185 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2185+point (1327/200) 4096 2186)/2)
    have hp : cPayment 2185 = (63421309270:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2185+point (1327/200) 4096 2186)/2 = (5580317:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2185
  · change cPayment 2186 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2186+point (1327/200) 4096 2187)/2)
    have hp : cPayment 2186 = (63391003473:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2186+point (1327/200) 4096 2187)/2 = (5581371:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2186
  · change cPayment 2187 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2187+point (1327/200) 4096 2188)/2)
    have hp : cPayment 2187 = (63360686550:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2187+point (1327/200) 4096 2188)/2 = (223297:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2187
  · change cPayment 2188 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2188+point (1327/200) 4096 2189)/2)
    have hp : cPayment 2188 = (63330358522:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2188+point (1327/200) 4096 2189)/2 = (5583479:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2188
  · change cPayment 2189 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2189+point (1327/200) 4096 2190)/2)
    have hp : cPayment 2189 = (63300019411:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2189+point (1327/200) 4096 2190)/2 = (5584533:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2189
  · change cPayment 2190 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2190+point (1327/200) 4096 2191)/2)
    have hp : cPayment 2190 = (63269669239:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2190+point (1327/200) 4096 2191)/2 = (5585587:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2190
  · change cPayment 2191 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2191+point (1327/200) 4096 2192)/2)
    have hp : cPayment 2191 = (63239308027:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2191+point (1327/200) 4096 2192)/2 = (5586641:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2191
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_136
