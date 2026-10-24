import WR2ClassicalCPayments
import WR2ClassicalCPoints219
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_219 (j : Fin 16) : cPayment (16*219+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*219+j.val)+point (1327/200) 4096 (16*219+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3504 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3504+point (1327/200) 4096 3505)/2)
    have hp : cPayment 3504 = (19391998443:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3504+point (1327/200) 4096 3505)/2 = (6970543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3504
  · change cPayment 3505 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3505+point (1327/200) 4096 3506)/2)
    have hp : cPayment 3505 = (19358358061:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3505+point (1327/200) 4096 3506)/2 = (6971597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3505
  · change cPayment 3506 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3506+point (1327/200) 4096 3507)/2)
    have hp : cPayment 3506 = (19324719996:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3506+point (1327/200) 4096 3507)/2 = (6972651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3506
  · change cPayment 3507 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3507+point (1327/200) 4096 3508)/2)
    have hp : cPayment 3507 = (19291084250:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3507+point (1327/200) 4096 3508)/2 = (1394741:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3507
  · change cPayment 3508 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3508+point (1327/200) 4096 3509)/2)
    have hp : cPayment 3508 = (19257450827:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3508+point (1327/200) 4096 3509)/2 = (6974759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3508
  · change cPayment 3509 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3509+point (1327/200) 4096 3510)/2)
    have hp : cPayment 3509 = (19223819732:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3509+point (1327/200) 4096 3510)/2 = (6975813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3509
  · change cPayment 3510 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3510+point (1327/200) 4096 3511)/2)
    have hp : cPayment 3510 = (19190190967:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3510+point (1327/200) 4096 3511)/2 = (6976867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3510
  · change cPayment 3511 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3511+point (1327/200) 4096 3512)/2)
    have hp : cPayment 3511 = (19156564537:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3511+point (1327/200) 4096 3512)/2 = (6977921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3511
  · change cPayment 3512 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3512+point (1327/200) 4096 3513)/2)
    have hp : cPayment 3512 = (19122940444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3512+point (1327/200) 4096 3513)/2 = (279159:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3512
  · change cPayment 3513 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3513+point (1327/200) 4096 3514)/2)
    have hp : cPayment 3513 = (19089318693:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3513+point (1327/200) 4096 3514)/2 = (6980029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3513
  · change cPayment 3514 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3514+point (1327/200) 4096 3515)/2)
    have hp : cPayment 3514 = (19055699287:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3514+point (1327/200) 4096 3515)/2 = (6981083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3514
  · change cPayment 3515 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3515+point (1327/200) 4096 3516)/2)
    have hp : cPayment 3515 = (19022082230:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3515+point (1327/200) 4096 3516)/2 = (6982137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3515
  · change cPayment 3516 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3516+point (1327/200) 4096 3517)/2)
    have hp : cPayment 3516 = (18988467525:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3516+point (1327/200) 4096 3517)/2 = (6983191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3516
  · change cPayment 3517 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3517+point (1327/200) 4096 3518)/2)
    have hp : cPayment 3517 = (18954855176:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3517+point (1327/200) 4096 3518)/2 = (1396849:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3517
  · change cPayment 3518 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3518+point (1327/200) 4096 3519)/2)
    have hp : cPayment 3518 = (18921245187:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3518+point (1327/200) 4096 3519)/2 = (6985299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3518
  · change cPayment 3519 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3519+point (1327/200) 4096 3520)/2)
    have hp : cPayment 3519 = (18887637560:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3519+point (1327/200) 4096 3520)/2 = (6986353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3519
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_219
