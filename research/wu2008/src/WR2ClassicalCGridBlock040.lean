import WR2ClassicalCPayments
import WR2ClassicalCPoints040
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_040 (j : Fin 16) : cPayment (16*40+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*40+j.val)+point (1327/200) 4096 (16*40+j.val+1))/2) := by
  fin_cases j
  · change cPayment 640 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 640+point (1327/200) 4096 641)/2)
    have hp : cPayment 640 = (71764900883:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 640+point (1327/200) 4096 641)/2 = (3951887:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_640
  · change cPayment 641 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 641+point (1327/200) 4096 642)/2)
    have hp : cPayment 641 = (71813481931:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 641+point (1327/200) 4096 642)/2 = (3952941:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_641
  · change cPayment 642 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 642+point (1327/200) 4096 643)/2)
    have hp : cPayment 642 = (71861927932:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 642+point (1327/200) 4096 643)/2 = (790799:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_642
  · change cPayment 643 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 643+point (1327/200) 4096 644)/2)
    have hp : cPayment 643 = (71910239102:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 643+point (1327/200) 4096 644)/2 = (3955049:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_643
  · change cPayment 644 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 644+point (1327/200) 4096 645)/2)
    have hp : cPayment 644 = (71958415653:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 644+point (1327/200) 4096 645)/2 = (3956103:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_644
  · change cPayment 645 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 645+point (1327/200) 4096 646)/2)
    have hp : cPayment 645 = (72006457799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 645+point (1327/200) 4096 646)/2 = (3957157:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_645
  · change cPayment 646 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 646+point (1327/200) 4096 647)/2)
    have hp : cPayment 646 = (72054365753:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 646+point (1327/200) 4096 647)/2 = (3958211:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_646
  · change cPayment 647 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 647+point (1327/200) 4096 648)/2)
    have hp : cPayment 647 = (72102139726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 647+point (1327/200) 4096 648)/2 = (791853:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_647
  · change cPayment 648 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 648+point (1327/200) 4096 649)/2)
    have hp : cPayment 648 = (72149779932:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 648+point (1327/200) 4096 649)/2 = (3960319:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_648
  · change cPayment 649 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 649+point (1327/200) 4096 650)/2)
    have hp : cPayment 649 = (72197286582:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 649+point (1327/200) 4096 650)/2 = (3961373:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_649
  · change cPayment 650 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 650+point (1327/200) 4096 651)/2)
    have hp : cPayment 650 = (72244659886:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 650+point (1327/200) 4096 651)/2 = (3962427:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_650
  · change cPayment 651 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 651+point (1327/200) 4096 652)/2)
    have hp : cPayment 651 = (72291900057:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 651+point (1327/200) 4096 652)/2 = (3963481:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_651
  · change cPayment 652 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 652+point (1327/200) 4096 653)/2)
    have hp : cPayment 652 = (72339007304:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 652+point (1327/200) 4096 653)/2 = (792907:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_652
  · change cPayment 653 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 653+point (1327/200) 4096 654)/2)
    have hp : cPayment 653 = (72385981839:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 653+point (1327/200) 4096 654)/2 = (3965589:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_653
  · change cPayment 654 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 654+point (1327/200) 4096 655)/2)
    have hp : cPayment 654 = (72432823871:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 654+point (1327/200) 4096 655)/2 = (3966643:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_654
  · change cPayment 655 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 655+point (1327/200) 4096 656)/2)
    have hp : cPayment 655 = (72479533609:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 655+point (1327/200) 4096 656)/2 = (3967697:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_655
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_040
