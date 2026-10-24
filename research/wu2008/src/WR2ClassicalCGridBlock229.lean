import WR2ClassicalCPayments
import WR2ClassicalCPoints229
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_229 (j : Fin 16) : cPayment (16*229+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*229+j.val)+point (1327/200) 4096 (16*229+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3664 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3664+point (1327/200) 4096 3665)/2)
    have hp : cPayment 3664 = (14041304758:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3664+point (1327/200) 4096 3665)/2 = (7139183:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3664
  · change cPayment 3665 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3665+point (1327/200) 4096 3666)/2)
    have hp : cPayment 3665 = (14008077915:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3665+point (1327/200) 4096 3666)/2 = (7140237:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3665
  · change cPayment 3666 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3666+point (1327/200) 4096 3667)/2)
    have hp : cPayment 3666 = (13974853908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3666+point (1327/200) 4096 3667)/2 = (7141291:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3666
  · change cPayment 3667 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3667+point (1327/200) 4096 3668)/2)
    have hp : cPayment 3667 = (13941632739:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3667+point (1327/200) 4096 3668)/2 = (1428469:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3667
  · change cPayment 3668 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3668+point (1327/200) 4096 3669)/2)
    have hp : cPayment 3668 = (13908414413:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3668+point (1327/200) 4096 3669)/2 = (7143399:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3668
  · change cPayment 3669 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3669+point (1327/200) 4096 3670)/2)
    have hp : cPayment 3669 = (13875198931:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3669+point (1327/200) 4096 3670)/2 = (7144453:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3669
  · change cPayment 3670 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3670+point (1327/200) 4096 3671)/2)
    have hp : cPayment 3670 = (13841986296:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3670+point (1327/200) 4096 3671)/2 = (7145507:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3670
  · change cPayment 3671 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3671+point (1327/200) 4096 3672)/2)
    have hp : cPayment 3671 = (13808776512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3671+point (1327/200) 4096 3672)/2 = (7146561:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3671
  · change cPayment 3672 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3672+point (1327/200) 4096 3673)/2)
    have hp : cPayment 3672 = (13775569581:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3672+point (1327/200) 4096 3673)/2 = (1429523:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3672
  · change cPayment 3673 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3673+point (1327/200) 4096 3674)/2)
    have hp : cPayment 3673 = (13742365506:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3673+point (1327/200) 4096 3674)/2 = (7148669:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3673
  · change cPayment 3674 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3674+point (1327/200) 4096 3675)/2)
    have hp : cPayment 3674 = (13709164290:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3674+point (1327/200) 4096 3675)/2 = (7149723:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3674
  · change cPayment 3675 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3675+point (1327/200) 4096 3676)/2)
    have hp : cPayment 3675 = (13675965935:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3675+point (1327/200) 4096 3676)/2 = (7150777:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3675
  · change cPayment 3676 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3676+point (1327/200) 4096 3677)/2)
    have hp : cPayment 3676 = (13642770445:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3676+point (1327/200) 4096 3677)/2 = (7151831:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3676
  · change cPayment 3677 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3677+point (1327/200) 4096 3678)/2)
    have hp : cPayment 3677 = (13609577823:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3677+point (1327/200) 4096 3678)/2 = (1430577:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3677
  · change cPayment 3678 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3678+point (1327/200) 4096 3679)/2)
    have hp : cPayment 3678 = (13576388071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3678+point (1327/200) 4096 3679)/2 = (7153939:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3678
  · change cPayment 3679 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3679+point (1327/200) 4096 3680)/2)
    have hp : cPayment 3679 = (13543201191:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3679+point (1327/200) 4096 3680)/2 = (7154993:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3679
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_229
