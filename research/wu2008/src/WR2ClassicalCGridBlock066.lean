import WR2ClassicalCPayments
import WR2ClassicalCPoints066
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_066 (j : Fin 16) : cPayment (16*66+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*66+j.val)+point (1327/200) 4096 (16*66+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1056 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1056+point (1327/200) 4096 1057)/2)
    have hp : cPayment 1056 = (82477456929:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1056+point (1327/200) 4096 1057)/2 = (4390351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1056
  · change cPayment 1057 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1057+point (1327/200) 4096 1058)/2)
    have hp : cPayment 1057 = (82484699767:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1057+point (1327/200) 4096 1058)/2 = (878281:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1057
  · change cPayment 1058 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1058+point (1327/200) 4096 1059)/2)
    have hp : cPayment 1058 = (82491871828:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1058+point (1327/200) 4096 1059)/2 = (4392459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1058
  · change cPayment 1059 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1059+point (1327/200) 4096 1060)/2)
    have hp : cPayment 1059 = (82498973221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1059+point (1327/200) 4096 1060)/2 = (4393513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1059
  · change cPayment 1060 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1060+point (1327/200) 4096 1061)/2)
    have hp : cPayment 1060 = (82506004053:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1060+point (1327/200) 4096 1061)/2 = (4394567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1060
  · change cPayment 1061 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1061+point (1327/200) 4096 1062)/2)
    have hp : cPayment 1061 = (82512964434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1061+point (1327/200) 4096 1062)/2 = (4395621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1061
  · change cPayment 1062 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1062+point (1327/200) 4096 1063)/2)
    have hp : cPayment 1062 = (82519854470:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1062+point (1327/200) 4096 1063)/2 = (175867:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1062
  · change cPayment 1063 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1063+point (1327/200) 4096 1064)/2)
    have hp : cPayment 1063 = (82526674270:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1063+point (1327/200) 4096 1064)/2 = (4397729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1063
  · change cPayment 1064 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1064+point (1327/200) 4096 1065)/2)
    have hp : cPayment 1064 = (82533423940:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1064+point (1327/200) 4096 1065)/2 = (4398783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1064
  · change cPayment 1065 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1065+point (1327/200) 4096 1066)/2)
    have hp : cPayment 1065 = (82540103590:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1065+point (1327/200) 4096 1066)/2 = (4399837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1065
  · change cPayment 1066 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1066+point (1327/200) 4096 1067)/2)
    have hp : cPayment 1066 = (82546713325:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1066+point (1327/200) 4096 1067)/2 = (4400891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1066
  · change cPayment 1067 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1067+point (1327/200) 4096 1068)/2)
    have hp : cPayment 1067 = (82553253253:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1067+point (1327/200) 4096 1068)/2 = (880389:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1067
  · change cPayment 1068 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1068+point (1327/200) 4096 1069)/2)
    have hp : cPayment 1068 = (82559723480:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1068+point (1327/200) 4096 1069)/2 = (4402999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1068
  · change cPayment 1069 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1069+point (1327/200) 4096 1070)/2)
    have hp : cPayment 1069 = (82566124114:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1069+point (1327/200) 4096 1070)/2 = (4404053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1069
  · change cPayment 1070 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1070+point (1327/200) 4096 1071)/2)
    have hp : cPayment 1070 = (82572455262:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1070+point (1327/200) 4096 1071)/2 = (4405107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1070
  · change cPayment 1071 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1071+point (1327/200) 4096 1072)/2)
    have hp : cPayment 1071 = (82578717028:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1071+point (1327/200) 4096 1072)/2 = (4406161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1071
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_066
