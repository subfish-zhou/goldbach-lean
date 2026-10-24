import WR2ClassicalCPayments
import WR2ClassicalCPoints069
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_069 (j : Fin 16) : cPayment (16*69+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*69+j.val)+point (1327/200) 4096 (16*69+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1104 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1104+point (1327/200) 4096 1105)/2)
    have hp : cPayment 1104 = (82747119725:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1104+point (1327/200) 4096 1105)/2 = (4440943:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1104
  · change cPayment 1105 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1105+point (1327/200) 4096 1106)/2)
    have hp : cPayment 1105 = (82751084708:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1105+point (1327/200) 4096 1106)/2 = (4441997:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1105
  · change cPayment 1106 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1106+point (1327/200) 4096 1107)/2)
    have hp : cPayment 1106 = (82754983934:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1106+point (1327/200) 4096 1107)/2 = (4443051:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1106
  · change cPayment 1107 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1107+point (1327/200) 4096 1108)/2)
    have hp : cPayment 1107 = (82758817502:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1107+point (1327/200) 4096 1108)/2 = (888821:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1107
  · change cPayment 1108 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1108+point (1327/200) 4096 1109)/2)
    have hp : cPayment 1108 = (82762585513:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1108+point (1327/200) 4096 1109)/2 = (4445159:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1108
  · change cPayment 1109 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1109+point (1327/200) 4096 1110)/2)
    have hp : cPayment 1109 = (82766288068:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1109+point (1327/200) 4096 1110)/2 = (4446213:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1109
  · change cPayment 1110 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1110+point (1327/200) 4096 1111)/2)
    have hp : cPayment 1110 = (82769925266:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1110+point (1327/200) 4096 1111)/2 = (4447267:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1110
  · change cPayment 1111 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1111+point (1327/200) 4096 1112)/2)
    have hp : cPayment 1111 = (82773497208:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1111+point (1327/200) 4096 1112)/2 = (4448321:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1111
  · change cPayment 1112 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1112+point (1327/200) 4096 1113)/2)
    have hp : cPayment 1112 = (82777003994:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1112+point (1327/200) 4096 1113)/2 = (177975:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1112
  · change cPayment 1113 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1113+point (1327/200) 4096 1114)/2)
    have hp : cPayment 1113 = (82780445722:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1113+point (1327/200) 4096 1114)/2 = (4450429:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1113
  · change cPayment 1114 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1114+point (1327/200) 4096 1115)/2)
    have hp : cPayment 1114 = (82783822494:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1114+point (1327/200) 4096 1115)/2 = (4451483:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1114
  · change cPayment 1115 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1115+point (1327/200) 4096 1116)/2)
    have hp : cPayment 1115 = (82787134408:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1115+point (1327/200) 4096 1116)/2 = (4452537:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1115
  · change cPayment 1116 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1116+point (1327/200) 4096 1117)/2)
    have hp : cPayment 1116 = (82790381563:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1116+point (1327/200) 4096 1117)/2 = (4453591:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1116
  · change cPayment 1117 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1117+point (1327/200) 4096 1118)/2)
    have hp : cPayment 1117 = (82793564059:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1117+point (1327/200) 4096 1118)/2 = (890929:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1117
  · change cPayment 1118 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1118+point (1327/200) 4096 1119)/2)
    have hp : cPayment 1118 = (82796681995:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1118+point (1327/200) 4096 1119)/2 = (4455699:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1118
  · change cPayment 1119 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1119+point (1327/200) 4096 1120)/2)
    have hp : cPayment 1119 = (82799735469:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1119+point (1327/200) 4096 1120)/2 = (4456753:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1119
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_069
