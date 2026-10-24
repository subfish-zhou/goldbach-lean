import WR2ClassicalCPayments
import WR2ClassicalCPoints222
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_222 (j : Fin 16) : cPayment (16*222+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*222+j.val)+point (1327/200) 4096 (16*222+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3552 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3552+point (1327/200) 4096 3553)/2)
    have hp : cPayment 3552 = (17779934677:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3552+point (1327/200) 4096 3553)/2 = (1404227:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3552
  · change cPayment 3553 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3553+point (1327/200) 4096 3554)/2)
    have hp : cPayment 3553 = (17746409487:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3553+point (1327/200) 4096 3554)/2 = (7022189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3553
  · change cPayment 3554 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3554+point (1327/200) 4096 3555)/2)
    have hp : cPayment 3554 = (17712886782:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3554+point (1327/200) 4096 3555)/2 = (7023243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3554
  · change cPayment 3555 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3555+point (1327/200) 4096 3556)/2)
    have hp : cPayment 3555 = (17679366565:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3555+point (1327/200) 4096 3556)/2 = (7024297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3555
  · change cPayment 3556 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3556+point (1327/200) 4096 3557)/2)
    have hp : cPayment 3556 = (17645848841:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3556+point (1327/200) 4096 3557)/2 = (7025351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3556
  · change cPayment 3557 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3557+point (1327/200) 4096 3558)/2)
    have hp : cPayment 3557 = (17612333611:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3557+point (1327/200) 4096 3558)/2 = (1405281:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3557
  · change cPayment 3558 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3558+point (1327/200) 4096 3559)/2)
    have hp : cPayment 3558 = (17578820881:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3558+point (1327/200) 4096 3559)/2 = (7027459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3558
  · change cPayment 3559 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3559+point (1327/200) 4096 3560)/2)
    have hp : cPayment 3559 = (17545310652:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3559+point (1327/200) 4096 3560)/2 = (7028513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3559
  · change cPayment 3560 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3560+point (1327/200) 4096 3561)/2)
    have hp : cPayment 3560 = (17511802929:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3560+point (1327/200) 4096 3561)/2 = (7029567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3560
  · change cPayment 3561 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3561+point (1327/200) 4096 3562)/2)
    have hp : cPayment 3561 = (17478297714:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3561+point (1327/200) 4096 3562)/2 = (7030621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3561
  · change cPayment 3562 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3562+point (1327/200) 4096 3563)/2)
    have hp : cPayment 3562 = (17444795012:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3562+point (1327/200) 4096 3563)/2 = (281267:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3562
  · change cPayment 3563 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3563+point (1327/200) 4096 3564)/2)
    have hp : cPayment 3563 = (17411294825:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3563+point (1327/200) 4096 3564)/2 = (7032729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3563
  · change cPayment 3564 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3564+point (1327/200) 4096 3565)/2)
    have hp : cPayment 3564 = (17377797157:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3564+point (1327/200) 4096 3565)/2 = (7033783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3564
  · change cPayment 3565 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3565+point (1327/200) 4096 3566)/2)
    have hp : cPayment 3565 = (17344302011:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3565+point (1327/200) 4096 3566)/2 = (7034837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3565
  · change cPayment 3566 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3566+point (1327/200) 4096 3567)/2)
    have hp : cPayment 3566 = (17310809390:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3566+point (1327/200) 4096 3567)/2 = (7035891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3566
  · change cPayment 3567 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3567+point (1327/200) 4096 3568)/2)
    have hp : cPayment 3567 = (17277319299:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3567+point (1327/200) 4096 3568)/2 = (1407389:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3567
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_222
