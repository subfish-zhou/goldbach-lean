import WR2ClassicalCPayments
import WR2ClassicalCPoints010
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_010 (j : Fin 16) : cPayment (16*10+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*10+j.val)+point (1327/200) 4096 (16*10+j.val+1))/2) := by
  fin_cases j
  · change cPayment 160 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 160+point (1327/200) 4096 161)/2)
    have hp : cPayment 160 = (27870007859:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 160+point (1327/200) 4096 161)/2 = (3445967:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_160
  · change cPayment 161 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 161+point (1327/200) 4096 162)/2)
    have hp : cPayment 161 = (28017035160:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 161+point (1327/200) 4096 162)/2 = (3447021:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_161
  · change cPayment 162 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 162+point (1327/200) 4096 163)/2)
    have hp : cPayment 162 = (28163763577:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 162+point (1327/200) 4096 163)/2 = (137923:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_162
  · change cPayment 163 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 163+point (1327/200) 4096 164)/2)
    have hp : cPayment 163 = (28310193630:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 163+point (1327/200) 4096 164)/2 = (3449129:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_163
  · change cPayment 164 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 164+point (1327/200) 4096 165)/2)
    have hp : cPayment 164 = (28456325839:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 164+point (1327/200) 4096 165)/2 = (3450183:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_164
  · change cPayment 165 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 165+point (1327/200) 4096 166)/2)
    have hp : cPayment 165 = (28602160723:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 165+point (1327/200) 4096 166)/2 = (3451237:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_165
  · change cPayment 166 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 166+point (1327/200) 4096 167)/2)
    have hp : cPayment 166 = (28747698801:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 166+point (1327/200) 4096 167)/2 = (3452291:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_166
  · change cPayment 167 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 167+point (1327/200) 4096 168)/2)
    have hp : cPayment 167 = (28892940589:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 167+point (1327/200) 4096 168)/2 = (690669:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_167
  · change cPayment 168 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 168+point (1327/200) 4096 169)/2)
    have hp : cPayment 168 = (29037886602:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 168+point (1327/200) 4096 169)/2 = (3454399:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_168
  · change cPayment 169 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 169+point (1327/200) 4096 170)/2)
    have hp : cPayment 169 = (29182537356:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 169+point (1327/200) 4096 170)/2 = (3455453:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_169
  · change cPayment 170 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 170+point (1327/200) 4096 171)/2)
    have hp : cPayment 170 = (29326893365:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 170+point (1327/200) 4096 171)/2 = (3456507:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_170
  · change cPayment 171 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 171+point (1327/200) 4096 172)/2)
    have hp : cPayment 171 = (29470955141:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 171+point (1327/200) 4096 172)/2 = (3457561:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_171
  · change cPayment 172 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 172+point (1327/200) 4096 173)/2)
    have hp : cPayment 172 = (29614723196:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 172+point (1327/200) 4096 173)/2 = (691723:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_172
  · change cPayment 173 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 173+point (1327/200) 4096 174)/2)
    have hp : cPayment 173 = (29758198041:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 173+point (1327/200) 4096 174)/2 = (3459669:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_173
  · change cPayment 174 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 174+point (1327/200) 4096 175)/2)
    have hp : cPayment 174 = (29901380185:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 174+point (1327/200) 4096 175)/2 = (3460723:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_174
  · change cPayment 175 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 175+point (1327/200) 4096 176)/2)
    have hp : cPayment 175 = (30044270137:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 175+point (1327/200) 4096 176)/2 = (3461777:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_175
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_010
