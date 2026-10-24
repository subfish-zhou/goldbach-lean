import WR2ClassicalCPayments
import WR2ClassicalCPoints044
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_044 (j : Fin 16) : cPayment (16*44+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*44+j.val)+point (1327/200) 4096 (16*44+j.val+1))/2) := by
  fin_cases j
  · change cPayment 704 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 704+point (1327/200) 4096 705)/2)
    have hp : cPayment 704 = (74610519613:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 704+point (1327/200) 4096 705)/2 = (4019343:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_704
  · change cPayment 705 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 705+point (1327/200) 4096 706)/2)
    have hp : cPayment 705 = (74650874100:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 705+point (1327/200) 4096 706)/2 = (4020397:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_705
  · change cPayment 706 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 706+point (1327/200) 4096 707)/2)
    have hp : cPayment 706 = (74691106520:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 706+point (1327/200) 4096 707)/2 = (4021451:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_706
  · change cPayment 707 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 707+point (1327/200) 4096 708)/2)
    have hp : cPayment 707 = (74731217064:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 707+point (1327/200) 4096 708)/2 = (804501:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_707
  · change cPayment 708 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 708+point (1327/200) 4096 709)/2)
    have hp : cPayment 708 = (74771205924:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 708+point (1327/200) 4096 709)/2 = (4023559:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_708
  · change cPayment 709 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 709+point (1327/200) 4096 710)/2)
    have hp : cPayment 709 = (74811073291:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 709+point (1327/200) 4096 710)/2 = (4024613:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_709
  · change cPayment 710 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 710+point (1327/200) 4096 711)/2)
    have hp : cPayment 710 = (74850819356:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 710+point (1327/200) 4096 711)/2 = (4025667:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_710
  · change cPayment 711 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 711+point (1327/200) 4096 712)/2)
    have hp : cPayment 711 = (74890444309:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 711+point (1327/200) 4096 712)/2 = (4026721:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_711
  · change cPayment 712 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 712+point (1327/200) 4096 713)/2)
    have hp : cPayment 712 = (74929948340:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 712+point (1327/200) 4096 713)/2 = (161111:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_712
  · change cPayment 713 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 713+point (1327/200) 4096 714)/2)
    have hp : cPayment 713 = (74969331640:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 713+point (1327/200) 4096 714)/2 = (4028829:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_713
  · change cPayment 714 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 714+point (1327/200) 4096 715)/2)
    have hp : cPayment 714 = (75008594398:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 714+point (1327/200) 4096 715)/2 = (4029883:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_714
  · change cPayment 715 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 715+point (1327/200) 4096 716)/2)
    have hp : cPayment 715 = (75047736803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 715+point (1327/200) 4096 716)/2 = (4030937:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_715
  · change cPayment 716 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 716+point (1327/200) 4096 717)/2)
    have hp : cPayment 716 = (75086759044:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 716+point (1327/200) 4096 717)/2 = (4031991:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_716
  · change cPayment 717 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 717+point (1327/200) 4096 718)/2)
    have hp : cPayment 717 = (75125661309:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 717+point (1327/200) 4096 718)/2 = (806609:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_717
  · change cPayment 718 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 718+point (1327/200) 4096 719)/2)
    have hp : cPayment 718 = (75164443787:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 718+point (1327/200) 4096 719)/2 = (4034099:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_718
  · change cPayment 719 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 719+point (1327/200) 4096 720)/2)
    have hp : cPayment 719 = (75203106666:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 719+point (1327/200) 4096 720)/2 = (4035153:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_719
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_044
