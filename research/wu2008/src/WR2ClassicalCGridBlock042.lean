import WR2ClassicalCPayments
import WR2ClassicalCPoints042
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_042 (j : Fin 16) : cPayment (16*42+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*42+j.val)+point (1327/200) 4096 (16*42+j.val+1))/2) := by
  fin_cases j
  · change cPayment 672 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 672+point (1327/200) 4096 673)/2)
    have hp : cPayment 672 = (73253559566:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 672+point (1327/200) 4096 673)/2 = (797123:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_672
  · change cPayment 673 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 673+point (1327/200) 4096 674)/2)
    have hp : cPayment 673 = (73297923447:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 673+point (1327/200) 4096 674)/2 = (3986669:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_673
  · change cPayment 674 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 674+point (1327/200) 4096 675)/2)
    have hp : cPayment 674 = (73342158949:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 674+point (1327/200) 4096 675)/2 = (3987723:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_674
  · change cPayment 675 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 675+point (1327/200) 4096 676)/2)
    have hp : cPayment 675 = (73386266273:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 675+point (1327/200) 4096 676)/2 = (3988777:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_675
  · change cPayment 676 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 676+point (1327/200) 4096 677)/2)
    have hp : cPayment 676 = (73430245622:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 676+point (1327/200) 4096 677)/2 = (3989831:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_676
  · change cPayment 677 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 677+point (1327/200) 4096 678)/2)
    have hp : cPayment 677 = (73474097199:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 677+point (1327/200) 4096 678)/2 = (798177:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_677
  · change cPayment 678 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 678+point (1327/200) 4096 679)/2)
    have hp : cPayment 678 = (73517821203:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 678+point (1327/200) 4096 679)/2 = (3991939:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_678
  · change cPayment 679 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 679+point (1327/200) 4096 680)/2)
    have hp : cPayment 679 = (73561417837:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 679+point (1327/200) 4096 680)/2 = (3992993:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_679
  · change cPayment 680 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 680+point (1327/200) 4096 681)/2)
    have hp : cPayment 680 = (73604887302:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 680+point (1327/200) 4096 681)/2 = (3994047:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_680
  · change cPayment 681 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 681+point (1327/200) 4096 682)/2)
    have hp : cPayment 681 = (73648229797:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 681+point (1327/200) 4096 682)/2 = (3995101:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_681
  · change cPayment 682 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 682+point (1327/200) 4096 683)/2)
    have hp : cPayment 682 = (73691445523:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 682+point (1327/200) 4096 683)/2 = (799231:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_682
  · change cPayment 683 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 683+point (1327/200) 4096 684)/2)
    have hp : cPayment 683 = (73734534679:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 683+point (1327/200) 4096 684)/2 = (3997209:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_683
  · change cPayment 684 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 684+point (1327/200) 4096 685)/2)
    have hp : cPayment 684 = (73777497465:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 684+point (1327/200) 4096 685)/2 = (3998263:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_684
  · change cPayment 685 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 685+point (1327/200) 4096 686)/2)
    have hp : cPayment 685 = (73820334081:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 685+point (1327/200) 4096 686)/2 = (3999317:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_685
  · change cPayment 686 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 686+point (1327/200) 4096 687)/2)
    have hp : cPayment 686 = (73863044724:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 686+point (1327/200) 4096 687)/2 = (4000371:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_686
  · change cPayment 687 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 687+point (1327/200) 4096 688)/2)
    have hp : cPayment 687 = (73905629594:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 687+point (1327/200) 4096 688)/2 = (160057:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_687
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_042
