import WR2ClassicalCPayments
import WR2ClassicalCPoints011
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_011 (j : Fin 16) : cPayment (16*11+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*11+j.val)+point (1327/200) 4096 (16*11+j.val+1))/2) := by
  fin_cases j
  · change cPayment 176 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 176+point (1327/200) 4096 177)/2)
    have hp : cPayment 176 = (30186868405:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 176+point (1327/200) 4096 177)/2 = (3462831:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_176
  · change cPayment 177 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 177+point (1327/200) 4096 178)/2)
    have hp : cPayment 177 = (30329175495:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 177+point (1327/200) 4096 178)/2 = (692777:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_177
  · change cPayment 178 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 178+point (1327/200) 4096 179)/2)
    have hp : cPayment 178 = (30471191913:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 178+point (1327/200) 4096 179)/2 = (3464939:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_178
  · change cPayment 179 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 179+point (1327/200) 4096 180)/2)
    have hp : cPayment 179 = (30612918164:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 179+point (1327/200) 4096 180)/2 = (3465993:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_179
  · change cPayment 180 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 180+point (1327/200) 4096 181)/2)
    have hp : cPayment 180 = (30754354750:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 180+point (1327/200) 4096 181)/2 = (3467047:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_180
  · change cPayment 181 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 181+point (1327/200) 4096 182)/2)
    have hp : cPayment 181 = (30895502175:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 181+point (1327/200) 4096 182)/2 = (3468101:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_181
  · change cPayment 182 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 182+point (1327/200) 4096 183)/2)
    have hp : cPayment 182 = (31036360940:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 182+point (1327/200) 4096 183)/2 = (693831:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_182
  · change cPayment 183 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 183+point (1327/200) 4096 184)/2)
    have hp : cPayment 183 = (31176931547:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 183+point (1327/200) 4096 184)/2 = (3470209:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_183
  · change cPayment 184 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 184+point (1327/200) 4096 185)/2)
    have hp : cPayment 184 = (31317214493:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 184+point (1327/200) 4096 185)/2 = (3471263:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_184
  · change cPayment 185 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 185+point (1327/200) 4096 186)/2)
    have hp : cPayment 185 = (31457210279:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 185+point (1327/200) 4096 186)/2 = (3472317:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_185
  · change cPayment 186 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 186+point (1327/200) 4096 187)/2)
    have hp : cPayment 186 = (31596919400:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 186+point (1327/200) 4096 187)/2 = (3473371:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_186
  · change cPayment 187 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 187+point (1327/200) 4096 188)/2)
    have hp : cPayment 187 = (31736342356:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 187+point (1327/200) 4096 188)/2 = (138977:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_187
  · change cPayment 188 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 188+point (1327/200) 4096 189)/2)
    have hp : cPayment 188 = (31875479639:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 188+point (1327/200) 4096 189)/2 = (3475479:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_188
  · change cPayment 189 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 189+point (1327/200) 4096 190)/2)
    have hp : cPayment 189 = (32014331746:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 189+point (1327/200) 4096 190)/2 = (3476533:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_189
  · change cPayment 190 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 190+point (1327/200) 4096 191)/2)
    have hp : cPayment 190 = (32152899170:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 190+point (1327/200) 4096 191)/2 = (3477587:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_190
  · change cPayment 191 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 191+point (1327/200) 4096 192)/2)
    have hp : cPayment 191 = (32291182404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 191+point (1327/200) 4096 192)/2 = (3478641:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_191
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_011
