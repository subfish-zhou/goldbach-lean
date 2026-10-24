import WR2ClassicalCPayments
import WR2ClassicalCPoints038
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_038 (j : Fin 16) : cPayment (16*38+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*38+j.val)+point (1327/200) 4096 (16*38+j.val+1))/2) := by
  fin_cases j
  · change cPayment 608 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 608+point (1327/200) 4096 609)/2)
    have hp : cPayment 608 = (70137703604:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 608+point (1327/200) 4096 609)/2 = (3918159:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_608
  · change cPayment 609 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 609+point (1327/200) 4096 610)/2)
    have hp : cPayment 609 = (70190721300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 609+point (1327/200) 4096 610)/2 = (3919213:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_609
  · change cPayment 610 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 610+point (1327/200) 4096 611)/2)
    have hp : cPayment 610 = (70243596908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 610+point (1327/200) 4096 611)/2 = (3920267:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_610
  · change cPayment 611 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 611+point (1327/200) 4096 612)/2)
    have hp : cPayment 611 = (70296330652:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 611+point (1327/200) 4096 612)/2 = (3921321:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_611
  · change cPayment 612 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 612+point (1327/200) 4096 613)/2)
    have hp : cPayment 612 = (70348922758:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 612+point (1327/200) 4096 613)/2 = (156895:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_612
  · change cPayment 613 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 613+point (1327/200) 4096 614)/2)
    have hp : cPayment 613 = (70401373451:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 613+point (1327/200) 4096 614)/2 = (3923429:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_613
  · change cPayment 614 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 614+point (1327/200) 4096 615)/2)
    have hp : cPayment 614 = (70453682958:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 614+point (1327/200) 4096 615)/2 = (3924483:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_614
  · change cPayment 615 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 615+point (1327/200) 4096 616)/2)
    have hp : cPayment 615 = (70505851501:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 615+point (1327/200) 4096 616)/2 = (3925537:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_615
  · change cPayment 616 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 616+point (1327/200) 4096 617)/2)
    have hp : cPayment 616 = (70557879305:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 616+point (1327/200) 4096 617)/2 = (3926591:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_616
  · change cPayment 617 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 617+point (1327/200) 4096 618)/2)
    have hp : cPayment 617 = (70609766594:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 617+point (1327/200) 4096 618)/2 = (785529:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_617
  · change cPayment 618 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 618+point (1327/200) 4096 619)/2)
    have hp : cPayment 618 = (70661513591:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 618+point (1327/200) 4096 619)/2 = (3928699:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_618
  · change cPayment 619 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 619+point (1327/200) 4096 620)/2)
    have hp : cPayment 619 = (70713120519:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 619+point (1327/200) 4096 620)/2 = (3929753:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_619
  · change cPayment 620 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 620+point (1327/200) 4096 621)/2)
    have hp : cPayment 620 = (70764587601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 620+point (1327/200) 4096 621)/2 = (3930807:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_620
  · change cPayment 621 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 621+point (1327/200) 4096 622)/2)
    have hp : cPayment 621 = (70815915059:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 621+point (1327/200) 4096 622)/2 = (3931861:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_621
  · change cPayment 622 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 622+point (1327/200) 4096 623)/2)
    have hp : cPayment 622 = (70867103115:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 622+point (1327/200) 4096 623)/2 = (786583:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_622
  · change cPayment 623 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 623+point (1327/200) 4096 624)/2)
    have hp : cPayment 623 = (70918151989:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 623+point (1327/200) 4096 624)/2 = (3933969:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_623
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_038
