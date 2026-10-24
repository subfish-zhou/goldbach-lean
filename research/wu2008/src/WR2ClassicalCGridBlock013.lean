import WR2ClassicalCPayments
import WR2ClassicalCPoints013
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_013 (j : Fin 16) : cPayment (16*13+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*13+j.val)+point (1327/200) 4096 (16*13+j.val+1))/2) := by
  fin_cases j
  · change cPayment 208 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 208+point (1327/200) 4096 209)/2)
    have hp : cPayment 208 = (34598988902:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 208+point (1327/200) 4096 209)/2 = (3496559:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_208
  · change cPayment 209 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 209+point (1327/200) 4096 210)/2)
    have hp : cPayment 209 = (34732239845:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 209+point (1327/200) 4096 210)/2 = (3497613:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_209
  · change cPayment 210 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 210+point (1327/200) 4096 211)/2)
    have hp : cPayment 210 = (34865215773:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 210+point (1327/200) 4096 211)/2 = (3498667:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_210
  · change cPayment 211 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 211+point (1327/200) 4096 212)/2)
    have hp : cPayment 211 = (34997917161:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 211+point (1327/200) 4096 212)/2 = (3499721:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_211
  · change cPayment 212 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 212+point (1327/200) 4096 213)/2)
    have hp : cPayment 212 = (35130344481:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 212+point (1327/200) 4096 213)/2 = (140031:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_212
  · change cPayment 213 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 213+point (1327/200) 4096 214)/2)
    have hp : cPayment 213 = (35262498204:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 213+point (1327/200) 4096 214)/2 = (3501829:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_213
  · change cPayment 214 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 214+point (1327/200) 4096 215)/2)
    have hp : cPayment 214 = (35394378803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 214+point (1327/200) 4096 215)/2 = (3502883:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_214
  · change cPayment 215 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 215+point (1327/200) 4096 216)/2)
    have hp : cPayment 215 = (35525986745:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 215+point (1327/200) 4096 216)/2 = (3503937:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_215
  · change cPayment 216 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 216+point (1327/200) 4096 217)/2)
    have hp : cPayment 216 = (35657322501:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 216+point (1327/200) 4096 217)/2 = (3504991:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_216
  · change cPayment 217 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 217+point (1327/200) 4096 218)/2)
    have hp : cPayment 217 = (35788386537:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 217+point (1327/200) 4096 218)/2 = (701209:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_217
  · change cPayment 218 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 218+point (1327/200) 4096 219)/2)
    have hp : cPayment 218 = (35919179321:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 218+point (1327/200) 4096 219)/2 = (3507099:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_218
  · change cPayment 219 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 219+point (1327/200) 4096 220)/2)
    have hp : cPayment 219 = (36049701319:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 219+point (1327/200) 4096 220)/2 = (3508153:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_219
  · change cPayment 220 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 220+point (1327/200) 4096 221)/2)
    have hp : cPayment 220 = (36179952996:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 220+point (1327/200) 4096 221)/2 = (3509207:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_220
  · change cPayment 221 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 221+point (1327/200) 4096 222)/2)
    have hp : cPayment 221 = (36309934817:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 221+point (1327/200) 4096 222)/2 = (3510261:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_221
  · change cPayment 222 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 222+point (1327/200) 4096 223)/2)
    have hp : cPayment 222 = (36439647244:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 222+point (1327/200) 4096 223)/2 = (702263:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_222
  · change cPayment 223 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 223+point (1327/200) 4096 224)/2)
    have hp : cPayment 223 = (36569090740:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 223+point (1327/200) 4096 224)/2 = (3512369:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_223
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_013
