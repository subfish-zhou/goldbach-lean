import WR2ClassicalCPayments
import WR2ClassicalCPoints114
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_114 (j : Fin 16) : cPayment (16*114+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*114+j.val)+point (1327/200) 4096 (16*114+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1824 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1824+point (1327/200) 4096 1825)/2)
    have hp : cPayment 1824 = (73440335006:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1824+point (1327/200) 4096 1825)/2 = (5199823:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1824
  · change cPayment 1825 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1825+point (1327/200) 4096 1826)/2)
    have hp : cPayment 1825 = (73415722453:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1825+point (1327/200) 4096 1826)/2 = (5200877:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1825
  · change cPayment 1826 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1826+point (1327/200) 4096 1827)/2)
    have hp : cPayment 1826 = (73391088692:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1826+point (1327/200) 4096 1827)/2 = (5201931:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1826
  · change cPayment 1827 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1827+point (1327/200) 4096 1828)/2)
    have hp : cPayment 1827 = (73366433757:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1827+point (1327/200) 4096 1828)/2 = (1040597:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1827
  · change cPayment 1828 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1828+point (1327/200) 4096 1829)/2)
    have hp : cPayment 1828 = (73341757683:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1828+point (1327/200) 4096 1829)/2 = (5204039:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1828
  · change cPayment 1829 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1829+point (1327/200) 4096 1830)/2)
    have hp : cPayment 1829 = (73317060506:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1829+point (1327/200) 4096 1830)/2 = (5205093:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1829
  · change cPayment 1830 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1830+point (1327/200) 4096 1831)/2)
    have hp : cPayment 1830 = (73292342261:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1830+point (1327/200) 4096 1831)/2 = (5206147:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1830
  · change cPayment 1831 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1831+point (1327/200) 4096 1832)/2)
    have hp : cPayment 1831 = (73267602983:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1831+point (1327/200) 4096 1832)/2 = (5207201:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1831
  · change cPayment 1832 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1832+point (1327/200) 4096 1833)/2)
    have hp : cPayment 1832 = (73242842708:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1832+point (1327/200) 4096 1833)/2 = (1041651:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1832
  · change cPayment 1833 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1833+point (1327/200) 4096 1834)/2)
    have hp : cPayment 1833 = (73218061469:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1833+point (1327/200) 4096 1834)/2 = (5209309:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1833
  · change cPayment 1834 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1834+point (1327/200) 4096 1835)/2)
    have hp : cPayment 1834 = (73193259304:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1834+point (1327/200) 4096 1835)/2 = (5210363:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1834
  · change cPayment 1835 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1835+point (1327/200) 4096 1836)/2)
    have hp : cPayment 1835 = (73168436245:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1835+point (1327/200) 4096 1836)/2 = (5211417:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1835
  · change cPayment 1836 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1836+point (1327/200) 4096 1837)/2)
    have hp : cPayment 1836 = (73143592329:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1836+point (1327/200) 4096 1837)/2 = (5212471:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1836
  · change cPayment 1837 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1837+point (1327/200) 4096 1838)/2)
    have hp : cPayment 1837 = (73118727590:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1837+point (1327/200) 4096 1838)/2 = (208541:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1837
  · change cPayment 1838 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1838+point (1327/200) 4096 1839)/2)
    have hp : cPayment 1838 = (73093842063:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1838+point (1327/200) 4096 1839)/2 = (5214579:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1838
  · change cPayment 1839 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1839+point (1327/200) 4096 1840)/2)
    have hp : cPayment 1839 = (73068935782:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1839+point (1327/200) 4096 1840)/2 = (5215633:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1839
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_114
