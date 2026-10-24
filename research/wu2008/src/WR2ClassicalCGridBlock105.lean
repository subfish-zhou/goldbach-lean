import WR2ClassicalCPayments
import WR2ClassicalCPoints105
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_105 (j : Fin 16) : cPayment (16*105+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*105+j.val)+point (1327/200) 4096 (16*105+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1680 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1680+point (1327/200) 4096 1681)/2)
    have hp : cPayment 1680 = (76744196832:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1680+point (1327/200) 4096 1681)/2 = (5048047:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1680
  · change cPayment 1681 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1681+point (1327/200) 4096 1682)/2)
    have hp : cPayment 1681 = (76723033850:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1681+point (1327/200) 4096 1682)/2 = (5049101:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1681
  · change cPayment 1682 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1682+point (1327/200) 4096 1683)/2)
    have hp : cPayment 1682 = (76701844018:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1682+point (1327/200) 4096 1683)/2 = (1010031:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1682
  · change cPayment 1683 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1683+point (1327/200) 4096 1684)/2)
    have hp : cPayment 1683 = (76680627377:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1683+point (1327/200) 4096 1684)/2 = (5051209:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1683
  · change cPayment 1684 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1684+point (1327/200) 4096 1685)/2)
    have hp : cPayment 1684 = (76659383973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1684+point (1327/200) 4096 1685)/2 = (5052263:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1684
  · change cPayment 1685 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1685+point (1327/200) 4096 1686)/2)
    have hp : cPayment 1685 = (76638113846:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1685+point (1327/200) 4096 1686)/2 = (5053317:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1685
  · change cPayment 1686 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1686+point (1327/200) 4096 1687)/2)
    have hp : cPayment 1686 = (76616817042:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1686+point (1327/200) 4096 1687)/2 = (5054371:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1686
  · change cPayment 1687 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1687+point (1327/200) 4096 1688)/2)
    have hp : cPayment 1687 = (76595493602:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1687+point (1327/200) 4096 1688)/2 = (202217:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1687
  · change cPayment 1688 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1688+point (1327/200) 4096 1689)/2)
    have hp : cPayment 1688 = (76574143569:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1688+point (1327/200) 4096 1689)/2 = (5056479:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1688
  · change cPayment 1689 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1689+point (1327/200) 4096 1690)/2)
    have hp : cPayment 1689 = (76552766987:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1689+point (1327/200) 4096 1690)/2 = (5057533:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1689
  · change cPayment 1690 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1690+point (1327/200) 4096 1691)/2)
    have hp : cPayment 1690 = (76531363898:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1690+point (1327/200) 4096 1691)/2 = (5058587:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1690
  · change cPayment 1691 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1691+point (1327/200) 4096 1692)/2)
    have hp : cPayment 1691 = (76509934345:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1691+point (1327/200) 4096 1692)/2 = (5059641:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1691
  · change cPayment 1692 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1692+point (1327/200) 4096 1693)/2)
    have hp : cPayment 1692 = (76488478371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1692+point (1327/200) 4096 1693)/2 = (1012139:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1692
  · change cPayment 1693 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1693+point (1327/200) 4096 1694)/2)
    have hp : cPayment 1693 = (76466996017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1693+point (1327/200) 4096 1694)/2 = (5061749:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1693
  · change cPayment 1694 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1694+point (1327/200) 4096 1695)/2)
    have hp : cPayment 1694 = (76445487328:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1694+point (1327/200) 4096 1695)/2 = (5062803:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1694
  · change cPayment 1695 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1695+point (1327/200) 4096 1696)/2)
    have hp : cPayment 1695 = (76423952345:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1695+point (1327/200) 4096 1696)/2 = (5063857:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1695
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_105
