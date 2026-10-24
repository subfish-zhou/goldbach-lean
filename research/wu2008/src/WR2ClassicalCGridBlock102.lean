import WR2ClassicalCPayments
import WR2ClassicalCPoints102
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_102 (j : Fin 16) : cPayment (16*102+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*102+j.val)+point (1327/200) 4096 (16*102+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1632 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1632+point (1327/200) 4096 1633)/2)
    have hp : cPayment 1632 = (77727580674:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1632+point (1327/200) 4096 1633)/2 = (999491:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1632
  · change cPayment 1633 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1633+point (1327/200) 4096 1634)/2)
    have hp : cPayment 1633 = (77707758581:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1633+point (1327/200) 4096 1634)/2 = (4998509:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1633
  · change cPayment 1634 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1634+point (1327/200) 4096 1635)/2)
    have hp : cPayment 1634 = (77687907489:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1634+point (1327/200) 4096 1635)/2 = (4999563:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1634
  · change cPayment 1635 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1635+point (1327/200) 4096 1636)/2)
    have hp : cPayment 1635 = (77668027444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1635+point (1327/200) 4096 1636)/2 = (5000617:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1635
  · change cPayment 1636 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1636+point (1327/200) 4096 1637)/2)
    have hp : cPayment 1636 = (77648118492:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1636+point (1327/200) 4096 1637)/2 = (5001671:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1636
  · change cPayment 1637 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1637+point (1327/200) 4096 1638)/2)
    have hp : cPayment 1637 = (77628180680:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1637+point (1327/200) 4096 1638)/2 = (200109:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1637
  · change cPayment 1638 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1638+point (1327/200) 4096 1639)/2)
    have hp : cPayment 1638 = (77608214054:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1638+point (1327/200) 4096 1639)/2 = (5003779:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1638
  · change cPayment 1639 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1639+point (1327/200) 4096 1640)/2)
    have hp : cPayment 1639 = (77588218660:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1639+point (1327/200) 4096 1640)/2 = (5004833:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1639
  · change cPayment 1640 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1640+point (1327/200) 4096 1641)/2)
    have hp : cPayment 1640 = (77568194543:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1640+point (1327/200) 4096 1641)/2 = (5005887:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1640
  · change cPayment 1641 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1641+point (1327/200) 4096 1642)/2)
    have hp : cPayment 1641 = (77548141750:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1641+point (1327/200) 4096 1642)/2 = (5006941:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1641
  · change cPayment 1642 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1642+point (1327/200) 4096 1643)/2)
    have hp : cPayment 1642 = (77528060326:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1642+point (1327/200) 4096 1643)/2 = (1001599:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1642
  · change cPayment 1643 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1643+point (1327/200) 4096 1644)/2)
    have hp : cPayment 1643 = (77507950317:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1643+point (1327/200) 4096 1644)/2 = (5009049:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1643
  · change cPayment 1644 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1644+point (1327/200) 4096 1645)/2)
    have hp : cPayment 1644 = (77487811769:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1644+point (1327/200) 4096 1645)/2 = (5010103:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1644
  · change cPayment 1645 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1645+point (1327/200) 4096 1646)/2)
    have hp : cPayment 1645 = (77467644727:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1645+point (1327/200) 4096 1646)/2 = (5011157:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1645
  · change cPayment 1646 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1646+point (1327/200) 4096 1647)/2)
    have hp : cPayment 1646 = (77447449237:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1646+point (1327/200) 4096 1647)/2 = (5012211:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1646
  · change cPayment 1647 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1647+point (1327/200) 4096 1648)/2)
    have hp : cPayment 1647 = (77427225344:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1647+point (1327/200) 4096 1648)/2 = (1002653:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1647
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_102
