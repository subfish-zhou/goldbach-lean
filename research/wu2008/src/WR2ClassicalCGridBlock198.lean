import WR2ClassicalCPayments
import WR2ClassicalCPoints198
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_198 (j : Fin 16) : cPayment (16*198+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*198+j.val)+point (1327/200) 4096 (16*198+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3168 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3168+point (1327/200) 4096 3169)/2)
    have hp : cPayment 3168 = (30799972375:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3168+point (1327/200) 4096 3169)/2 = (6616399:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3168
  · change cPayment 3169 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3169+point (1327/200) 4096 3170)/2)
    have hp : cPayment 3169 = (30765797267:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3169+point (1327/200) 4096 3170)/2 = (6617453:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3169
  · change cPayment 3170 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3170+point (1327/200) 4096 3171)/2)
    have hp : cPayment 3170 = (30731622909:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3170+point (1327/200) 4096 3171)/2 = (6618507:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3170
  · change cPayment 3171 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3171+point (1327/200) 4096 3172)/2)
    have hp : cPayment 3171 = (30697449305:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3171+point (1327/200) 4096 3172)/2 = (6619561:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3171
  · change cPayment 3172 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3172+point (1327/200) 4096 3173)/2)
    have hp : cPayment 3172 = (30663276462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3172+point (1327/200) 4096 3173)/2 = (1324123:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3172
  · change cPayment 3173 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3173+point (1327/200) 4096 3174)/2)
    have hp : cPayment 3173 = (30629104385:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3173+point (1327/200) 4096 3174)/2 = (6621669:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3173
  · change cPayment 3174 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3174+point (1327/200) 4096 3175)/2)
    have hp : cPayment 3174 = (30594933082:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3174+point (1327/200) 4096 3175)/2 = (6622723:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3174
  · change cPayment 3175 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3175+point (1327/200) 4096 3176)/2)
    have hp : cPayment 3175 = (30560762556:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3175+point (1327/200) 4096 3176)/2 = (6623777:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3175
  · change cPayment 3176 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3176+point (1327/200) 4096 3177)/2)
    have hp : cPayment 3176 = (30526592814:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3176+point (1327/200) 4096 3177)/2 = (6624831:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3176
  · change cPayment 3177 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3177+point (1327/200) 4096 3178)/2)
    have hp : cPayment 3177 = (30492423863:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3177+point (1327/200) 4096 3178)/2 = (1325177:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3177
  · change cPayment 3178 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3178+point (1327/200) 4096 3179)/2)
    have hp : cPayment 3178 = (30458255706:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3178+point (1327/200) 4096 3179)/2 = (6626939:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3178
  · change cPayment 3179 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3179+point (1327/200) 4096 3180)/2)
    have hp : cPayment 3179 = (30424088352:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3179+point (1327/200) 4096 3180)/2 = (6627993:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3179
  · change cPayment 3180 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3180+point (1327/200) 4096 3181)/2)
    have hp : cPayment 3180 = (30389921804:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3180+point (1327/200) 4096 3181)/2 = (6629047:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3180
  · change cPayment 3181 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3181+point (1327/200) 4096 3182)/2)
    have hp : cPayment 3181 = (30355756069:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3181+point (1327/200) 4096 3182)/2 = (6630101:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3181
  · change cPayment 3182 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3182+point (1327/200) 4096 3183)/2)
    have hp : cPayment 3182 = (30321591153:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3182+point (1327/200) 4096 3183)/2 = (1326231:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3182
  · change cPayment 3183 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3183+point (1327/200) 4096 3184)/2)
    have hp : cPayment 3183 = (30287427061:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3183+point (1327/200) 4096 3184)/2 = (6632209:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3183
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_198
