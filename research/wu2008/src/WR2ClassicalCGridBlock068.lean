import WR2ClassicalCPayments
import WR2ClassicalCPoints068
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_068 (j : Fin 16) : cPayment (16*68+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*68+j.val)+point (1327/200) 4096 (16*68+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1088 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1088+point (1327/200) 4096 1089)/2)
    have hp : cPayment 1088 = (82674654164:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1088+point (1327/200) 4096 1089)/2 = (4424079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1088
  · change cPayment 1089 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1089+point (1327/200) 4096 1090)/2)
    have hp : cPayment 1089 = (82679685091:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1089+point (1327/200) 4096 1090)/2 = (4425133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1089
  · change cPayment 1090 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1090+point (1327/200) 4096 1091)/2)
    have hp : cPayment 1090 = (82684648629:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1090+point (1327/200) 4096 1091)/2 = (4426187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1090
  · change cPayment 1091 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1091+point (1327/200) 4096 1092)/2)
    have hp : cPayment 1091 = (82689544881:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1091+point (1327/200) 4096 1092)/2 = (4427241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1091
  · change cPayment 1092 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1092+point (1327/200) 4096 1093)/2)
    have hp : cPayment 1092 = (82694373948:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1092+point (1327/200) 4096 1093)/2 = (885659:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1092
  · change cPayment 1093 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1093+point (1327/200) 4096 1094)/2)
    have hp : cPayment 1093 = (82699135935:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1093+point (1327/200) 4096 1094)/2 = (4429349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1093
  · change cPayment 1094 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1094+point (1327/200) 4096 1095)/2)
    have hp : cPayment 1094 = (82703830944:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1094+point (1327/200) 4096 1095)/2 = (4430403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1094
  · change cPayment 1095 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1095+point (1327/200) 4096 1096)/2)
    have hp : cPayment 1095 = (82708459078:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1095+point (1327/200) 4096 1096)/2 = (4431457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1095
  · change cPayment 1096 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1096+point (1327/200) 4096 1097)/2)
    have hp : cPayment 1096 = (82713020439:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1096+point (1327/200) 4096 1097)/2 = (4432511:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1096
  · change cPayment 1097 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1097+point (1327/200) 4096 1098)/2)
    have hp : cPayment 1097 = (82717515128:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1097+point (1327/200) 4096 1098)/2 = (886713:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1097
  · change cPayment 1098 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1098+point (1327/200) 4096 1099)/2)
    have hp : cPayment 1098 = (82721943249:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1098+point (1327/200) 4096 1099)/2 = (4434619:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1098
  · change cPayment 1099 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1099+point (1327/200) 4096 1100)/2)
    have hp : cPayment 1099 = (82726304903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1099+point (1327/200) 4096 1100)/2 = (4435673:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1099
  · change cPayment 1100 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1100+point (1327/200) 4096 1101)/2)
    have hp : cPayment 1100 = (82730600192:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1100+point (1327/200) 4096 1101)/2 = (4436727:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1100
  · change cPayment 1101 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1101+point (1327/200) 4096 1102)/2)
    have hp : cPayment 1101 = (82734829217:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1101+point (1327/200) 4096 1102)/2 = (4437781:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1101
  · change cPayment 1102 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1102+point (1327/200) 4096 1103)/2)
    have hp : cPayment 1102 = (82738992080:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1102+point (1327/200) 4096 1103)/2 = (887767:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1102
  · change cPayment 1103 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1103+point (1327/200) 4096 1104)/2)
    have hp : cPayment 1103 = (82743088882:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1103+point (1327/200) 4096 1104)/2 = (4439889:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1103
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_068
