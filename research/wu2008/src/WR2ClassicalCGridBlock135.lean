import WR2ClassicalCPayments
import WR2ClassicalCPoints135
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_135 (j : Fin 16) : cPayment (16*135+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*135+j.val)+point (1327/200) 4096 (16*135+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2160 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2160+point (1327/200) 4096 2161)/2)
    have hp : cPayment 2160 = (64175274247:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2160+point (1327/200) 4096 2161)/2 = (5553967:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2160
  · change cPayment 2161 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2161+point (1327/200) 4096 2162)/2)
    have hp : cPayment 2161 = (64145253727:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2161+point (1327/200) 4096 2162)/2 = (5555021:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2161
  · change cPayment 2162 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2162+point (1327/200) 4096 2163)/2)
    have hp : cPayment 2162 = (64115221530:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2162+point (1327/200) 4096 2163)/2 = (222243:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2162
  · change cPayment 2163 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2163+point (1327/200) 4096 2164)/2)
    have hp : cPayment 2163 = (64085177679:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2163+point (1327/200) 4096 2164)/2 = (5557129:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2163
  · change cPayment 2164 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2164+point (1327/200) 4096 2165)/2)
    have hp : cPayment 2164 = (64055122195:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2164+point (1327/200) 4096 2165)/2 = (5558183:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2164
  · change cPayment 2165 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2165+point (1327/200) 4096 2166)/2)
    have hp : cPayment 2165 = (64025055101:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2165+point (1327/200) 4096 2166)/2 = (5559237:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2165
  · change cPayment 2166 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2166+point (1327/200) 4096 2167)/2)
    have hp : cPayment 2166 = (63994976420:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2166+point (1327/200) 4096 2167)/2 = (5560291:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2166
  · change cPayment 2167 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2167+point (1327/200) 4096 2168)/2)
    have hp : cPayment 2167 = (63964886174:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2167+point (1327/200) 4096 2168)/2 = (1112269:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2167
  · change cPayment 2168 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2168+point (1327/200) 4096 2169)/2)
    have hp : cPayment 2168 = (63934784384:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2168+point (1327/200) 4096 2169)/2 = (5562399:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2168
  · change cPayment 2169 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2169+point (1327/200) 4096 2170)/2)
    have hp : cPayment 2169 = (63904671074:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2169+point (1327/200) 4096 2170)/2 = (5563453:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2169
  · change cPayment 2170 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2170+point (1327/200) 4096 2171)/2)
    have hp : cPayment 2170 = (63874546265:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2170+point (1327/200) 4096 2171)/2 = (5564507:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2170
  · change cPayment 2171 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2171+point (1327/200) 4096 2172)/2)
    have hp : cPayment 2171 = (63844409979:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2171+point (1327/200) 4096 2172)/2 = (5565561:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2171
  · change cPayment 2172 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2172+point (1327/200) 4096 2173)/2)
    have hp : cPayment 2172 = (63814262239:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2172+point (1327/200) 4096 2173)/2 = (1113323:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2172
  · change cPayment 2173 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2173+point (1327/200) 4096 2174)/2)
    have hp : cPayment 2173 = (63784103066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2173+point (1327/200) 4096 2174)/2 = (5567669:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2173
  · change cPayment 2174 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2174+point (1327/200) 4096 2175)/2)
    have hp : cPayment 2174 = (63753932483:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2174+point (1327/200) 4096 2175)/2 = (5568723:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2174
  · change cPayment 2175 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2175+point (1327/200) 4096 2176)/2)
    have hp : cPayment 2175 = (63723750512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2175+point (1327/200) 4096 2176)/2 = (5569777:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2175
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_135
