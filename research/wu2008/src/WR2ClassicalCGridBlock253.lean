import WR2ClassicalCPayments
import WR2ClassicalCPoints253
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_253 (j : Fin 16) : cPayment (16*253+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*253+j.val)+point (1327/200) 4096 (16*253+j.val+1))/2) := by
  fin_cases j
  · change cPayment 4048 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4048+point (1327/200) 4096 4049)/2)
    have hp : cPayment 4048 = (1514147369:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4048+point (1327/200) 4096 4049)/2 = (7543919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4048
  · change cPayment 4049 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4049+point (1327/200) 4096 4050)/2)
    have hp : cPayment 4049 = (1482184812:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4049+point (1327/200) 4096 4050)/2 = (7544973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4049
  · change cPayment 4050 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4050+point (1327/200) 4096 4051)/2)
    have hp : cPayment 4050 = (1450225921:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4050+point (1327/200) 4096 4051)/2 = (7546027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4050
  · change cPayment 4051 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4051+point (1327/200) 4096 4052)/2)
    have hp : cPayment 4051 = (1418270697:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4051+point (1327/200) 4096 4052)/2 = (7547081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4051
  · change cPayment 4052 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4052+point (1327/200) 4096 4053)/2)
    have hp : cPayment 4052 = (1386319142:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4052+point (1327/200) 4096 4053)/2 = (1509627:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4052
  · change cPayment 4053 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4053+point (1327/200) 4096 4054)/2)
    have hp : cPayment 4053 = (1354371258:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4053+point (1327/200) 4096 4054)/2 = (7549189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4053
  · change cPayment 4054 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4054+point (1327/200) 4096 4055)/2)
    have hp : cPayment 4054 = (1322427047:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4054+point (1327/200) 4096 4055)/2 = (7550243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4054
  · change cPayment 4055 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4055+point (1327/200) 4096 4056)/2)
    have hp : cPayment 4055 = (1290486509:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4055+point (1327/200) 4096 4056)/2 = (7551297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4055
  · change cPayment 4056 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4056+point (1327/200) 4096 4057)/2)
    have hp : cPayment 4056 = (1258549646:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4056+point (1327/200) 4096 4057)/2 = (7552351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4056
  · change cPayment 4057 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4057+point (1327/200) 4096 4058)/2)
    have hp : cPayment 4057 = (1226616460:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4057+point (1327/200) 4096 4058)/2 = (1510681:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4057
  · change cPayment 4058 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4058+point (1327/200) 4096 4059)/2)
    have hp : cPayment 4058 = (1194686953:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4058+point (1327/200) 4096 4059)/2 = (7554459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4058
  · change cPayment 4059 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4059+point (1327/200) 4096 4060)/2)
    have hp : cPayment 4059 = (1162761125:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4059+point (1327/200) 4096 4060)/2 = (7555513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4059
  · change cPayment 4060 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4060+point (1327/200) 4096 4061)/2)
    have hp : cPayment 4060 = (1130838979:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4060+point (1327/200) 4096 4061)/2 = (7556567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4060
  · change cPayment 4061 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4061+point (1327/200) 4096 4062)/2)
    have hp : cPayment 4061 = (1098920516:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4061+point (1327/200) 4096 4062)/2 = (7557621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4061
  · change cPayment 4062 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4062+point (1327/200) 4096 4063)/2)
    have hp : cPayment 4062 = (1067005738:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4062+point (1327/200) 4096 4063)/2 = (302347:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4062
  · change cPayment 4063 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4063+point (1327/200) 4096 4064)/2)
    have hp : cPayment 4063 = (1035094645:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4063+point (1327/200) 4096 4064)/2 = (7559729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4063
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_253
