import WR2ClassicalCPayments
import WR2ClassicalCPoints118
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_118 (j : Fin 16) : cPayment (16*118+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*118+j.val)+point (1327/200) 4096 (16*118+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1888 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1888+point (1327/200) 4096 1889)/2)
    have hp : cPayment 1888 = (71823816880:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1888+point (1327/200) 4096 1889)/2 = (5267279:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1888
  · change cPayment 1889 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1889+point (1327/200) 4096 1890)/2)
    have hp : cPayment 1889 = (71797916244:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1889+point (1327/200) 4096 1890)/2 = (5268333:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1889
  · change cPayment 1890 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1890+point (1327/200) 4096 1891)/2)
    have hp : cPayment 1890 = (71771996568:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1890+point (1327/200) 4096 1891)/2 = (5269387:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1890
  · change cPayment 1891 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1891+point (1327/200) 4096 1892)/2)
    have hp : cPayment 1891 = (71746057882:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1891+point (1327/200) 4096 1892)/2 = (5270441:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1891
  · change cPayment 1892 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1892+point (1327/200) 4096 1893)/2)
    have hp : cPayment 1892 = (71720100219:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1892+point (1327/200) 4096 1893)/2 = (1054299:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1892
  · change cPayment 1893 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1893+point (1327/200) 4096 1894)/2)
    have hp : cPayment 1893 = (71694123613:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1893+point (1327/200) 4096 1894)/2 = (5272549:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1893
  · change cPayment 1894 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1894+point (1327/200) 4096 1895)/2)
    have hp : cPayment 1894 = (71668128094:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1894+point (1327/200) 4096 1895)/2 = (5273603:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1894
  · change cPayment 1895 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1895+point (1327/200) 4096 1896)/2)
    have hp : cPayment 1895 = (71642113695:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1895+point (1327/200) 4096 1896)/2 = (5274657:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1895
  · change cPayment 1896 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1896+point (1327/200) 4096 1897)/2)
    have hp : cPayment 1896 = (71616080448:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1896+point (1327/200) 4096 1897)/2 = (5275711:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1896
  · change cPayment 1897 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1897+point (1327/200) 4096 1898)/2)
    have hp : cPayment 1897 = (71590028386:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1897+point (1327/200) 4096 1898)/2 = (1055353:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1897
  · change cPayment 1898 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1898+point (1327/200) 4096 1899)/2)
    have hp : cPayment 1898 = (71563957540:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1898+point (1327/200) 4096 1899)/2 = (5277819:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1898
  · change cPayment 1899 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1899+point (1327/200) 4096 1900)/2)
    have hp : cPayment 1899 = (71537867942:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1899+point (1327/200) 4096 1900)/2 = (5278873:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1899
  · change cPayment 1900 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1900+point (1327/200) 4096 1901)/2)
    have hp : cPayment 1900 = (71511759625:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1900+point (1327/200) 4096 1901)/2 = (5279927:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1900
  · change cPayment 1901 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1901+point (1327/200) 4096 1902)/2)
    have hp : cPayment 1901 = (71485632620:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1901+point (1327/200) 4096 1902)/2 = (5280981:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1901
  · change cPayment 1902 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1902+point (1327/200) 4096 1903)/2)
    have hp : cPayment 1902 = (71459486959:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1902+point (1327/200) 4096 1903)/2 = (1056407:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1902
  · change cPayment 1903 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1903+point (1327/200) 4096 1904)/2)
    have hp : cPayment 1903 = (71433322675:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1903+point (1327/200) 4096 1904)/2 = (5283089:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1903
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_118
