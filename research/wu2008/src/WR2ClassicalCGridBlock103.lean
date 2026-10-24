import WR2ClassicalCPayments
import WR2ClassicalCPoints103
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_103 (j : Fin 16) : cPayment (16*103+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*103+j.val)+point (1327/200) 4096 (16*103+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1648 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1648+point (1327/200) 4096 1649)/2)
    have hp : cPayment 1648 = (77406973094:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1648+point (1327/200) 4096 1649)/2 = (5014319:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1648
  · change cPayment 1649 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1649+point (1327/200) 4096 1650)/2)
    have hp : cPayment 1649 = (77386692532:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1649+point (1327/200) 4096 1650)/2 = (5015373:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1649
  · change cPayment 1650 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1650+point (1327/200) 4096 1651)/2)
    have hp : cPayment 1650 = (77366383703:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1650+point (1327/200) 4096 1651)/2 = (5016427:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1650
  · change cPayment 1651 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1651+point (1327/200) 4096 1652)/2)
    have hp : cPayment 1651 = (77346046653:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1651+point (1327/200) 4096 1652)/2 = (5017481:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1651
  · change cPayment 1652 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1652+point (1327/200) 4096 1653)/2)
    have hp : cPayment 1652 = (77325681427:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1652+point (1327/200) 4096 1653)/2 = (1003707:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1652
  · change cPayment 1653 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1653+point (1327/200) 4096 1654)/2)
    have hp : cPayment 1653 = (77305288069:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1653+point (1327/200) 4096 1654)/2 = (5019589:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1653
  · change cPayment 1654 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1654+point (1327/200) 4096 1655)/2)
    have hp : cPayment 1654 = (77284866625:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1654+point (1327/200) 4096 1655)/2 = (5020643:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1654
  · change cPayment 1655 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1655+point (1327/200) 4096 1656)/2)
    have hp : cPayment 1655 = (77264417140:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1655+point (1327/200) 4096 1656)/2 = (5021697:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1655
  · change cPayment 1656 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1656+point (1327/200) 4096 1657)/2)
    have hp : cPayment 1656 = (77243939658:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1656+point (1327/200) 4096 1657)/2 = (5022751:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1656
  · change cPayment 1657 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1657+point (1327/200) 4096 1658)/2)
    have hp : cPayment 1657 = (77223434225:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1657+point (1327/200) 4096 1658)/2 = (1004761:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1657
  · change cPayment 1658 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1658+point (1327/200) 4096 1659)/2)
    have hp : cPayment 1658 = (77202900885:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1658+point (1327/200) 4096 1659)/2 = (5024859:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1658
  · change cPayment 1659 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1659+point (1327/200) 4096 1660)/2)
    have hp : cPayment 1659 = (77182339684:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1659+point (1327/200) 4096 1660)/2 = (5025913:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1659
  · change cPayment 1660 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1660+point (1327/200) 4096 1661)/2)
    have hp : cPayment 1660 = (77161750665:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1660+point (1327/200) 4096 1661)/2 = (5026967:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1660
  · change cPayment 1661 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1661+point (1327/200) 4096 1662)/2)
    have hp : cPayment 1661 = (77141133873:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1661+point (1327/200) 4096 1662)/2 = (5028021:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1661
  · change cPayment 1662 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1662+point (1327/200) 4096 1663)/2)
    have hp : cPayment 1662 = (77120489352:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1662+point (1327/200) 4096 1663)/2 = (201163:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1662
  · change cPayment 1663 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1663+point (1327/200) 4096 1664)/2)
    have hp : cPayment 1663 = (77099817148:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1663+point (1327/200) 4096 1664)/2 = (5030129:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1663
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_103
