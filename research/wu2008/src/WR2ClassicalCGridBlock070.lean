import WR2ClassicalCPayments
import WR2ClassicalCPoints070
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_070 (j : Fin 16) : cPayment (16*70+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*70+j.val)+point (1327/200) 4096 (16*70+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1120 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1120+point (1327/200) 4096 1121)/2)
    have hp : cPayment 1120 = (82802724580:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1120+point (1327/200) 4096 1121)/2 = (4457807:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1120
  · change cPayment 1121 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1121+point (1327/200) 4096 1122)/2)
    have hp : cPayment 1121 = (82805649426:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1121+point (1327/200) 4096 1122)/2 = (4458861:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1121
  · change cPayment 1122 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1122+point (1327/200) 4096 1123)/2)
    have hp : cPayment 1122 = (82808510107:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1122+point (1327/200) 4096 1123)/2 = (891983:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1122
  · change cPayment 1123 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1123+point (1327/200) 4096 1124)/2)
    have hp : cPayment 1123 = (82811306719:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1123+point (1327/200) 4096 1124)/2 = (4460969:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1123
  · change cPayment 1124 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1124+point (1327/200) 4096 1125)/2)
    have hp : cPayment 1124 = (82814039362:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1124+point (1327/200) 4096 1125)/2 = (4462023:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1124
  · change cPayment 1125 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1125+point (1327/200) 4096 1126)/2)
    have hp : cPayment 1125 = (82816708133:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1125+point (1327/200) 4096 1126)/2 = (4463077:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1125
  · change cPayment 1126 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1126+point (1327/200) 4096 1127)/2)
    have hp : cPayment 1126 = (82819313129:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1126+point (1327/200) 4096 1127)/2 = (4464131:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1126
  · change cPayment 1127 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1127+point (1327/200) 4096 1128)/2)
    have hp : cPayment 1127 = (82821854449:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1127+point (1327/200) 4096 1128)/2 = (893037:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1127
  · change cPayment 1128 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1128+point (1327/200) 4096 1129)/2)
    have hp : cPayment 1128 = (82824332189:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1128+point (1327/200) 4096 1129)/2 = (4466239:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1128
  · change cPayment 1129 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1129+point (1327/200) 4096 1130)/2)
    have hp : cPayment 1129 = (82826746448:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1129+point (1327/200) 4096 1130)/2 = (4467293:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1129
  · change cPayment 1130 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1130+point (1327/200) 4096 1131)/2)
    have hp : cPayment 1130 = (82829097322:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1130+point (1327/200) 4096 1131)/2 = (4468347:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1130
  · change cPayment 1131 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1131+point (1327/200) 4096 1132)/2)
    have hp : cPayment 1131 = (82831384908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1131+point (1327/200) 4096 1132)/2 = (4469401:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1131
  · change cPayment 1132 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1132+point (1327/200) 4096 1133)/2)
    have hp : cPayment 1132 = (82833609303:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1132+point (1327/200) 4096 1133)/2 = (894091:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1132
  · change cPayment 1133 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1133+point (1327/200) 4096 1134)/2)
    have hp : cPayment 1133 = (82835770604:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1133+point (1327/200) 4096 1134)/2 = (4471509:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1133
  · change cPayment 1134 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1134+point (1327/200) 4096 1135)/2)
    have hp : cPayment 1134 = (82837868908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1134+point (1327/200) 4096 1135)/2 = (4472563:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1134
  · change cPayment 1135 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1135+point (1327/200) 4096 1136)/2)
    have hp : cPayment 1135 = (82839904310:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1135+point (1327/200) 4096 1136)/2 = (4473617:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1135
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_070
