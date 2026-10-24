import WR2ClassicalCPayments
import WR2ClassicalCPoints116
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_116 (j : Fin 16) : cPayment (16*116+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*116+j.val)+point (1327/200) 4096 (16*116+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1856 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1856+point (1327/200) 4096 1857)/2)
    have hp : cPayment 1856 = (72642387245:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1856+point (1327/200) 4096 1857)/2 = (5233551:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1856
  · change cPayment 1857 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1857+point (1327/200) 4096 1858)/2)
    have hp : cPayment 1857 = (72617113300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1857+point (1327/200) 4096 1858)/2 = (1046921:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1857
  · change cPayment 1858 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1858+point (1327/200) 4096 1859)/2)
    have hp : cPayment 1858 = (72591819254:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1858+point (1327/200) 4096 1859)/2 = (5235659:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1858
  · change cPayment 1859 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1859+point (1327/200) 4096 1860)/2)
    have hp : cPayment 1859 = (72566505140:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1859+point (1327/200) 4096 1860)/2 = (5236713:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1859
  · change cPayment 1860 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1860+point (1327/200) 4096 1861)/2)
    have hp : cPayment 1860 = (72541170992:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1860+point (1327/200) 4096 1861)/2 = (5237767:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1860
  · change cPayment 1861 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1861+point (1327/200) 4096 1862)/2)
    have hp : cPayment 1861 = (72515816844:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1861+point (1327/200) 4096 1862)/2 = (5238821:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1861
  · change cPayment 1862 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1862+point (1327/200) 4096 1863)/2)
    have hp : cPayment 1862 = (72490442730:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1862+point (1327/200) 4096 1863)/2 = (209595:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1862
  · change cPayment 1863 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1863+point (1327/200) 4096 1864)/2)
    have hp : cPayment 1863 = (72465048683:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1863+point (1327/200) 4096 1864)/2 = (5240929:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1863
  · change cPayment 1864 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1864+point (1327/200) 4096 1865)/2)
    have hp : cPayment 1864 = (72439634737:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1864+point (1327/200) 4096 1865)/2 = (5241983:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1864
  · change cPayment 1865 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1865+point (1327/200) 4096 1866)/2)
    have hp : cPayment 1865 = (72414200926:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1865+point (1327/200) 4096 1866)/2 = (5243037:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1865
  · change cPayment 1866 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1866+point (1327/200) 4096 1867)/2)
    have hp : cPayment 1866 = (72388747283:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1866+point (1327/200) 4096 1867)/2 = (5244091:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1866
  · change cPayment 1867 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1867+point (1327/200) 4096 1868)/2)
    have hp : cPayment 1867 = (72363273841:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1867+point (1327/200) 4096 1868)/2 = (1049029:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1867
  · change cPayment 1868 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1868+point (1327/200) 4096 1869)/2)
    have hp : cPayment 1868 = (72337780634:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1868+point (1327/200) 4096 1869)/2 = (5246199:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1868
  · change cPayment 1869 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1869+point (1327/200) 4096 1870)/2)
    have hp : cPayment 1869 = (72312267695:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1869+point (1327/200) 4096 1870)/2 = (5247253:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1869
  · change cPayment 1870 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1870+point (1327/200) 4096 1871)/2)
    have hp : cPayment 1870 = (72286735058:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1870+point (1327/200) 4096 1871)/2 = (5248307:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1870
  · change cPayment 1871 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1871+point (1327/200) 4096 1872)/2)
    have hp : cPayment 1871 = (72261182755:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1871+point (1327/200) 4096 1872)/2 = (5249361:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1871
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_116
