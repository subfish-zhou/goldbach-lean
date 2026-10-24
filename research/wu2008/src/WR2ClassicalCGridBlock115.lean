import WR2ClassicalCPayments
import WR2ClassicalCPoints115
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_115 (j : Fin 16) : cPayment (16*115+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*115+j.val)+point (1327/200) 4096 (16*115+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1840 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1840+point (1327/200) 4096 1841)/2)
    have hp : cPayment 1840 = (73044008783:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1840+point (1327/200) 4096 1841)/2 = (5216687:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1840
  · change cPayment 1841 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1841+point (1327/200) 4096 1842)/2)
    have hp : cPayment 1841 = (73019061101:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1841+point (1327/200) 4096 1842)/2 = (5217741:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1841
  · change cPayment 1842 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1842+point (1327/200) 4096 1843)/2)
    have hp : cPayment 1842 = (72994092769:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1842+point (1327/200) 4096 1843)/2 = (1043759:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1842
  · change cPayment 1843 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1843+point (1327/200) 4096 1844)/2)
    have hp : cPayment 1843 = (72969103823:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1843+point (1327/200) 4096 1844)/2 = (5219849:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1843
  · change cPayment 1844 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1844+point (1327/200) 4096 1845)/2)
    have hp : cPayment 1844 = (72944094296:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1844+point (1327/200) 4096 1845)/2 = (5220903:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1844
  · change cPayment 1845 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1845+point (1327/200) 4096 1846)/2)
    have hp : cPayment 1845 = (72919064224:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1845+point (1327/200) 4096 1846)/2 = (5221957:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1845
  · change cPayment 1846 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1846+point (1327/200) 4096 1847)/2)
    have hp : cPayment 1846 = (72894013641:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1846+point (1327/200) 4096 1847)/2 = (5223011:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1846
  · change cPayment 1847 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1847+point (1327/200) 4096 1848)/2)
    have hp : cPayment 1847 = (72868942581:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1847+point (1327/200) 4096 1848)/2 = (1044813:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1847
  · change cPayment 1848 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1848+point (1327/200) 4096 1849)/2)
    have hp : cPayment 1848 = (72843851079:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1848+point (1327/200) 4096 1849)/2 = (5225119:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1848
  · change cPayment 1849 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1849+point (1327/200) 4096 1850)/2)
    have hp : cPayment 1849 = (72818739169:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1849+point (1327/200) 4096 1850)/2 = (5226173:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1849
  · change cPayment 1850 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1850+point (1327/200) 4096 1851)/2)
    have hp : cPayment 1850 = (72793606885:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1850+point (1327/200) 4096 1851)/2 = (5227227:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1850
  · change cPayment 1851 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1851+point (1327/200) 4096 1852)/2)
    have hp : cPayment 1851 = (72768454262:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1851+point (1327/200) 4096 1852)/2 = (5228281:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1851
  · change cPayment 1852 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1852+point (1327/200) 4096 1853)/2)
    have hp : cPayment 1852 = (72743281333:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1852+point (1327/200) 4096 1853)/2 = (1045867:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1852
  · change cPayment 1853 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1853+point (1327/200) 4096 1854)/2)
    have hp : cPayment 1853 = (72718088133:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1853+point (1327/200) 4096 1854)/2 = (5230389:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1853
  · change cPayment 1854 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1854+point (1327/200) 4096 1855)/2)
    have hp : cPayment 1854 = (72692874695:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1854+point (1327/200) 4096 1855)/2 = (5231443:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1854
  · change cPayment 1855 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1855+point (1327/200) 4096 1856)/2)
    have hp : cPayment 1855 = (72667641055:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1855+point (1327/200) 4096 1856)/2 = (5232497:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1855
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_115
