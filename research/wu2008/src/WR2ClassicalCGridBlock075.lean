import WR2ClassicalCPayments
import WR2ClassicalCPoints075
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_075 (j : Fin 16) : cPayment (16*75+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*75+j.val)+point (1327/200) 4096 (16*75+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1200 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1200+point (1327/200) 4096 1201)/2)
    have hp : cPayment 1200 = (82841782913:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1200+point (1327/200) 4096 1201)/2 = (4542127:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1200
  · change cPayment 1201 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1201+point (1327/200) 4096 1202)/2)
    have hp : cPayment 1201 = (82839872786:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1201+point (1327/200) 4096 1202)/2 = (4543181:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1201
  · change cPayment 1202 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1202+point (1327/200) 4096 1203)/2)
    have hp : cPayment 1202 = (82837905892:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1202+point (1327/200) 4096 1203)/2 = (908847:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1202
  · change cPayment 1203 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1203+point (1327/200) 4096 1204)/2)
    have hp : cPayment 1203 = (82835882320:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1203+point (1327/200) 4096 1204)/2 = (4545289:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1203
  · change cPayment 1204 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1204+point (1327/200) 4096 1205)/2)
    have hp : cPayment 1204 = (82833802155:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1204+point (1327/200) 4096 1205)/2 = (4546343:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1204
  · change cPayment 1205 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1205+point (1327/200) 4096 1206)/2)
    have hp : cPayment 1205 = (82831665484:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1205+point (1327/200) 4096 1206)/2 = (4547397:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1205
  · change cPayment 1206 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1206+point (1327/200) 4096 1207)/2)
    have hp : cPayment 1206 = (82829472393:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1206+point (1327/200) 4096 1207)/2 = (4548451:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1206
  · change cPayment 1207 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1207+point (1327/200) 4096 1208)/2)
    have hp : cPayment 1207 = (82827222970:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1207+point (1327/200) 4096 1208)/2 = (909901:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1207
  · change cPayment 1208 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1208+point (1327/200) 4096 1209)/2)
    have hp : cPayment 1208 = (82824917300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1208+point (1327/200) 4096 1209)/2 = (4550559:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1208
  · change cPayment 1209 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1209+point (1327/200) 4096 1210)/2)
    have hp : cPayment 1209 = (82822555470:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1209+point (1327/200) 4096 1210)/2 = (4551613:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1209
  · change cPayment 1210 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1210+point (1327/200) 4096 1211)/2)
    have hp : cPayment 1210 = (82820137565:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1210+point (1327/200) 4096 1211)/2 = (4552667:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1210
  · change cPayment 1211 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1211+point (1327/200) 4096 1212)/2)
    have hp : cPayment 1211 = (82817663671:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1211+point (1327/200) 4096 1212)/2 = (4553721:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1211
  · change cPayment 1212 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1212+point (1327/200) 4096 1213)/2)
    have hp : cPayment 1212 = (82815133875:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1212+point (1327/200) 4096 1213)/2 = (182191:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1212
  · change cPayment 1213 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1213+point (1327/200) 4096 1214)/2)
    have hp : cPayment 1213 = (82812548261:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1213+point (1327/200) 4096 1214)/2 = (4555829:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1213
  · change cPayment 1214 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1214+point (1327/200) 4096 1215)/2)
    have hp : cPayment 1214 = (82809906915:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1214+point (1327/200) 4096 1215)/2 = (4556883:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1214
  · change cPayment 1215 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1215+point (1327/200) 4096 1216)/2)
    have hp : cPayment 1215 = (82807209923:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1215+point (1327/200) 4096 1216)/2 = (4557937:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1215
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_075
