import WR2ClassicalCPayments
import WR2ClassicalCPoints225
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_225 (j : Fin 16) : cPayment (16*225+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*225+j.val)+point (1327/200) 4096 (16*225+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3600 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3600+point (1327/200) 4096 3601)/2)
    have hp : cPayment 3600 = (16173586521:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3600+point (1327/200) 4096 3601)/2 = (7071727:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3600
  · change cPayment 3601 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3601+point (1327/200) 4096 3602)/2)
    have hp : cPayment 3601 = (16140184361:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3601+point (1327/200) 4096 3602)/2 = (7072781:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3601
  · change cPayment 3602 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3602+point (1327/200) 4096 3603)/2)
    have hp : cPayment 3602 = (16106784844:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3602+point (1327/200) 4096 3603)/2 = (1414767:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3602
  · change cPayment 3603 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3603+point (1327/200) 4096 3604)/2)
    have hp : cPayment 3603 = (16073387973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3603+point (1327/200) 4096 3604)/2 = (7074889:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3603
  · change cPayment 3604 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3604+point (1327/200) 4096 3605)/2)
    have hp : cPayment 3604 = (16039993751:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3604+point (1327/200) 4096 3605)/2 = (7075943:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3604
  · change cPayment 3605 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3605+point (1327/200) 4096 3606)/2)
    have hp : cPayment 3605 = (16006602181:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3605+point (1327/200) 4096 3606)/2 = (7076997:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3605
  · change cPayment 3606 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3606+point (1327/200) 4096 3607)/2)
    have hp : cPayment 3606 = (15973213266:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3606+point (1327/200) 4096 3607)/2 = (7078051:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3606
  · change cPayment 3607 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3607+point (1327/200) 4096 3608)/2)
    have hp : cPayment 3607 = (15939827010:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3607+point (1327/200) 4096 3608)/2 = (1415821:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3607
  · change cPayment 3608 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3608+point (1327/200) 4096 3609)/2)
    have hp : cPayment 3608 = (15906443415:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3608+point (1327/200) 4096 3609)/2 = (7080159:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3608
  · change cPayment 3609 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3609+point (1327/200) 4096 3610)/2)
    have hp : cPayment 3609 = (15873062485:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3609+point (1327/200) 4096 3610)/2 = (7081213:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3609
  · change cPayment 3610 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3610+point (1327/200) 4096 3611)/2)
    have hp : cPayment 3610 = (15839684222:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3610+point (1327/200) 4096 3611)/2 = (7082267:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3610
  · change cPayment 3611 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3611+point (1327/200) 4096 3612)/2)
    have hp : cPayment 3611 = (15806308631:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3611+point (1327/200) 4096 3612)/2 = (7083321:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3611
  · change cPayment 3612 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3612+point (1327/200) 4096 3613)/2)
    have hp : cPayment 3612 = (15772935713:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3612+point (1327/200) 4096 3613)/2 = (283375:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3612
  · change cPayment 3613 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3613+point (1327/200) 4096 3614)/2)
    have hp : cPayment 3613 = (15739565473:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3613+point (1327/200) 4096 3614)/2 = (7085429:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3613
  · change cPayment 3614 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3614+point (1327/200) 4096 3615)/2)
    have hp : cPayment 3614 = (15706197913:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3614+point (1327/200) 4096 3615)/2 = (7086483:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3614
  · change cPayment 3615 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3615+point (1327/200) 4096 3616)/2)
    have hp : cPayment 3615 = (15672833037:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3615+point (1327/200) 4096 3616)/2 = (7087537:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3615
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_225
