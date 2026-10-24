import WR2ClassicalCPayments
import WR2ClassicalCPoints065
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_065 (j : Fin 16) : cPayment (16*65+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*65+j.val)+point (1327/200) 4096 (16*65+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1040 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1040+point (1327/200) 4096 1041)/2)
    have hp : cPayment 1040 = (82351856735:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1040+point (1327/200) 4096 1041)/2 = (4373487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1040
  · change cPayment 1041 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1041+point (1327/200) 4096 1042)/2)
    have hp : cPayment 1041 = (82360246887:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1041+point (1327/200) 4096 1042)/2 = (4374541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1041
  · change cPayment 1042 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1042+point (1327/200) 4096 1043)/2)
    have hp : cPayment 1042 = (82368564504:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1042+point (1327/200) 4096 1043)/2 = (875119:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1042
  · change cPayment 1043 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1043+point (1327/200) 4096 1044)/2)
    have hp : cPayment 1043 = (82376809698:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1043+point (1327/200) 4096 1044)/2 = (4376649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1043
  · change cPayment 1044 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1044+point (1327/200) 4096 1045)/2)
    have hp : cPayment 1044 = (82384982579:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1044+point (1327/200) 4096 1045)/2 = (4377703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1044
  · change cPayment 1045 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1045+point (1327/200) 4096 1046)/2)
    have hp : cPayment 1045 = (82393083258:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1045+point (1327/200) 4096 1046)/2 = (4378757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1045
  · change cPayment 1046 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1046+point (1327/200) 4096 1047)/2)
    have hp : cPayment 1046 = (82401111846:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1046+point (1327/200) 4096 1047)/2 = (4379811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1046
  · change cPayment 1047 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1047+point (1327/200) 4096 1048)/2)
    have hp : cPayment 1047 = (82409068454:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1047+point (1327/200) 4096 1048)/2 = (876173:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1047
  · change cPayment 1048 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1048+point (1327/200) 4096 1049)/2)
    have hp : cPayment 1048 = (82416953190:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1048+point (1327/200) 4096 1049)/2 = (4381919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1048
  · change cPayment 1049 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1049+point (1327/200) 4096 1050)/2)
    have hp : cPayment 1049 = (82424766167:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1049+point (1327/200) 4096 1050)/2 = (4382973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1049
  · change cPayment 1050 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1050+point (1327/200) 4096 1051)/2)
    have hp : cPayment 1050 = (82432507493:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1050+point (1327/200) 4096 1051)/2 = (4384027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1050
  · change cPayment 1051 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1051+point (1327/200) 4096 1052)/2)
    have hp : cPayment 1051 = (82440177279:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1051+point (1327/200) 4096 1052)/2 = (4385081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1051
  · change cPayment 1052 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1052+point (1327/200) 4096 1053)/2)
    have hp : cPayment 1052 = (82447775634:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1052+point (1327/200) 4096 1053)/2 = (877227:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1052
  · change cPayment 1053 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1053+point (1327/200) 4096 1054)/2)
    have hp : cPayment 1053 = (82455302667:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1053+point (1327/200) 4096 1054)/2 = (4387189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1053
  · change cPayment 1054 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1054+point (1327/200) 4096 1055)/2)
    have hp : cPayment 1054 = (82462758488:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1054+point (1327/200) 4096 1055)/2 = (4388243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1054
  · change cPayment 1055 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1055+point (1327/200) 4096 1056)/2)
    have hp : cPayment 1055 = (82470143205:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1055+point (1327/200) 4096 1056)/2 = (4389297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1055
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_065
