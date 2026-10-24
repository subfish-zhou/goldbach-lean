import WR2ClassicalCPayments
import WR2ClassicalCPoints076
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_076 (j : Fin 16) : cPayment (16*76+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*76+j.val)+point (1327/200) 4096 (16*76+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1216 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1216+point (1327/200) 4096 1217)/2)
    have hp : cPayment 1216 = (82804457370:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1216+point (1327/200) 4096 1217)/2 = (4558991:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1216
  · change cPayment 1217 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1217+point (1327/200) 4096 1218)/2)
    have hp : cPayment 1217 = (82801649341:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1217+point (1327/200) 4096 1218)/2 = (912009:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1217
  · change cPayment 1218 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1218+point (1327/200) 4096 1219)/2)
    have hp : cPayment 1218 = (82798785920:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1218+point (1327/200) 4096 1219)/2 = (4561099:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1218
  · change cPayment 1219 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1219+point (1327/200) 4096 1220)/2)
    have hp : cPayment 1219 = (82795867193:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1219+point (1327/200) 4096 1220)/2 = (4562153:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1219
  · change cPayment 1220 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1220+point (1327/200) 4096 1221)/2)
    have hp : cPayment 1220 = (82792893245:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1220+point (1327/200) 4096 1221)/2 = (4563207:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1220
  · change cPayment 1221 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1221+point (1327/200) 4096 1222)/2)
    have hp : cPayment 1221 = (82789864159:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1221+point (1327/200) 4096 1222)/2 = (4564261:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1221
  · change cPayment 1222 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1222+point (1327/200) 4096 1223)/2)
    have hp : cPayment 1222 = (82786780021:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1222+point (1327/200) 4096 1223)/2 = (913063:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1222
  · change cPayment 1223 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1223+point (1327/200) 4096 1224)/2)
    have hp : cPayment 1223 = (82783640915:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1223+point (1327/200) 4096 1224)/2 = (4566369:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1223
  · change cPayment 1224 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1224+point (1327/200) 4096 1225)/2)
    have hp : cPayment 1224 = (82780446925:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1224+point (1327/200) 4096 1225)/2 = (4567423:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1224
  · change cPayment 1225 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1225+point (1327/200) 4096 1226)/2)
    have hp : cPayment 1225 = (82777198134:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1225+point (1327/200) 4096 1226)/2 = (4568477:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1225
  · change cPayment 1226 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1226+point (1327/200) 4096 1227)/2)
    have hp : cPayment 1226 = (82773894628:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1226+point (1327/200) 4096 1227)/2 = (4569531:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1226
  · change cPayment 1227 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1227+point (1327/200) 4096 1228)/2)
    have hp : cPayment 1227 = (82770536490:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1227+point (1327/200) 4096 1228)/2 = (914117:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1227
  · change cPayment 1228 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1228+point (1327/200) 4096 1229)/2)
    have hp : cPayment 1228 = (82767123803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1228+point (1327/200) 4096 1229)/2 = (4571639:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1228
  · change cPayment 1229 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1229+point (1327/200) 4096 1230)/2)
    have hp : cPayment 1229 = (82763656651:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1229+point (1327/200) 4096 1230)/2 = (4572693:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1229
  · change cPayment 1230 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1230+point (1327/200) 4096 1231)/2)
    have hp : cPayment 1230 = (82760135117:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1230+point (1327/200) 4096 1231)/2 = (4573747:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1230
  · change cPayment 1231 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1231+point (1327/200) 4096 1232)/2)
    have hp : cPayment 1231 = (82756559286:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1231+point (1327/200) 4096 1232)/2 = (4574801:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1231
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_076
