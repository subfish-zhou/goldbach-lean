import WR2ClassicalCPayments
import WR2ClassicalCPoints003
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_003 (j : Fin 16) : cPayment (16*3+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*3+j.val)+point (1327/200) 4096 (16*3+j.val+1))/2) := by
  fin_cases j
  · change cPayment 48 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 48+point (1327/200) 4096 49)/2)
    have hp : cPayment 48 = (9378632634:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 48+point (1327/200) 4096 49)/2 = (3327919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_48
  · change cPayment 49 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 49+point (1327/200) 4096 50)/2)
    have hp : cPayment 49 = (9562703112:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 49+point (1327/200) 4096 50)/2 = (3328973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_49
  · change cPayment 50 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 50+point (1327/200) 4096 51)/2)
    have hp : cPayment 50 = (9746409052:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 50+point (1327/200) 4096 51)/2 = (3330027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_50
  · change cPayment 51 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 51+point (1327/200) 4096 52)/2)
    have hp : cPayment 51 = (9929751109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 51+point (1327/200) 4096 52)/2 = (3331081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_51
  · change cPayment 52 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 52+point (1327/200) 4096 53)/2)
    have hp : cPayment 52 = (10112729940:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 52+point (1327/200) 4096 53)/2 = (666427:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_52
  · change cPayment 53 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 53+point (1327/200) 4096 54)/2)
    have hp : cPayment 53 = (10295346198:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 53+point (1327/200) 4096 54)/2 = (3333189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_53
  · change cPayment 54 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 54+point (1327/200) 4096 55)/2)
    have hp : cPayment 54 = (10477600534:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 54+point (1327/200) 4096 55)/2 = (3334243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_54
  · change cPayment 55 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 55+point (1327/200) 4096 56)/2)
    have hp : cPayment 55 = (10659493599:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 55+point (1327/200) 4096 56)/2 = (3335297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_55
  · change cPayment 56 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 56+point (1327/200) 4096 57)/2)
    have hp : cPayment 56 = (10841026044:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 56+point (1327/200) 4096 57)/2 = (3336351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_56
  · change cPayment 57 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 57+point (1327/200) 4096 58)/2)
    have hp : cPayment 57 = (11022198515:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 57+point (1327/200) 4096 58)/2 = (667481:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_57
  · change cPayment 58 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 58+point (1327/200) 4096 59)/2)
    have hp : cPayment 58 = (11203011661:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 58+point (1327/200) 4096 59)/2 = (3338459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_58
  · change cPayment 59 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 59+point (1327/200) 4096 60)/2)
    have hp : cPayment 59 = (11383466126:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 59+point (1327/200) 4096 60)/2 = (3339513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_59
  · change cPayment 60 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 60+point (1327/200) 4096 61)/2)
    have hp : cPayment 60 = (11563562553:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 60+point (1327/200) 4096 61)/2 = (3340567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_60
  · change cPayment 61 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 61+point (1327/200) 4096 62)/2)
    have hp : cPayment 61 = (11743301587:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 61+point (1327/200) 4096 62)/2 = (3341621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_61
  · change cPayment 62 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 62+point (1327/200) 4096 63)/2)
    have hp : cPayment 62 = (11922683868:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 62+point (1327/200) 4096 63)/2 = (133707:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_62
  · change cPayment 63 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 63+point (1327/200) 4096 64)/2)
    have hp : cPayment 63 = (12101710037:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 63+point (1327/200) 4096 64)/2 = (3343729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_63
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_003
