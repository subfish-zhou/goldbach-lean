import WR2ClassicalCPayments
import WR2ClassicalCPoints067
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_067 (j : Fin 16) : cPayment (16*67+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*67+j.val)+point (1327/200) 4096 (16*67+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1072 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1072+point (1327/200) 4096 1073)/2)
    have hp : cPayment 1072 = (82584909521:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1072+point (1327/200) 4096 1073)/2 = (881443:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1072
  · change cPayment 1073 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1073+point (1327/200) 4096 1074)/2)
    have hp : cPayment 1073 = (82591032845:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1073+point (1327/200) 4096 1074)/2 = (4408269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1073
  · change cPayment 1074 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1074+point (1327/200) 4096 1075)/2)
    have hp : cPayment 1074 = (82597087107:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1074+point (1327/200) 4096 1075)/2 = (4409323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1074
  · change cPayment 1075 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1075+point (1327/200) 4096 1076)/2)
    have hp : cPayment 1075 = (82603072413:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1075+point (1327/200) 4096 1076)/2 = (4410377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1075
  · change cPayment 1076 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1076+point (1327/200) 4096 1077)/2)
    have hp : cPayment 1076 = (82608988867:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1076+point (1327/200) 4096 1077)/2 = (4411431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1076
  · change cPayment 1077 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1077+point (1327/200) 4096 1078)/2)
    have hp : cPayment 1077 = (82614836576:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1077+point (1327/200) 4096 1078)/2 = (882497:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1077
  · change cPayment 1078 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1078+point (1327/200) 4096 1079)/2)
    have hp : cPayment 1078 = (82620615645:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1078+point (1327/200) 4096 1079)/2 = (4413539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1078
  · change cPayment 1079 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1079+point (1327/200) 4096 1080)/2)
    have hp : cPayment 1079 = (82626326179:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1079+point (1327/200) 4096 1080)/2 = (4414593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1079
  · change cPayment 1080 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1080+point (1327/200) 4096 1081)/2)
    have hp : cPayment 1080 = (82631968283:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1080+point (1327/200) 4096 1081)/2 = (4415647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1080
  · change cPayment 1081 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1081+point (1327/200) 4096 1082)/2)
    have hp : cPayment 1081 = (82637542061:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1081+point (1327/200) 4096 1082)/2 = (4416701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1081
  · change cPayment 1082 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1082+point (1327/200) 4096 1083)/2)
    have hp : cPayment 1082 = (82643047618:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1082+point (1327/200) 4096 1083)/2 = (883551:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1082
  · change cPayment 1083 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1083+point (1327/200) 4096 1084)/2)
    have hp : cPayment 1083 = (82648485059:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1083+point (1327/200) 4096 1084)/2 = (4418809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1083
  · change cPayment 1084 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1084+point (1327/200) 4096 1085)/2)
    have hp : cPayment 1084 = (82653854488:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1084+point (1327/200) 4096 1085)/2 = (4419863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1084
  · change cPayment 1085 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1085+point (1327/200) 4096 1086)/2)
    have hp : cPayment 1085 = (82659156009:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1085+point (1327/200) 4096 1086)/2 = (4420917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1085
  · change cPayment 1086 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1086+point (1327/200) 4096 1087)/2)
    have hp : cPayment 1086 = (82664389726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1086+point (1327/200) 4096 1087)/2 = (4421971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1086
  · change cPayment 1087 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1087+point (1327/200) 4096 1088)/2)
    have hp : cPayment 1087 = (82669555743:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1087+point (1327/200) 4096 1088)/2 = (176921:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1087
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_067
