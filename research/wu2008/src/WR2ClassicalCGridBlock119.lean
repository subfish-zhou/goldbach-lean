import WR2ClassicalCPayments
import WR2ClassicalCPoints119
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_119 (j : Fin 16) : cPayment (16*119+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*119+j.val)+point (1327/200) 4096 (16*119+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1904 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1904+point (1327/200) 4096 1905)/2)
    have hp : cPayment 1904 = (71407139798:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1904+point (1327/200) 4096 1905)/2 = (5284143:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1904
  · change cPayment 1905 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1905+point (1327/200) 4096 1906)/2)
    have hp : cPayment 1905 = (71380938362:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1905+point (1327/200) 4096 1906)/2 = (5285197:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1905
  · change cPayment 1906 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1906+point (1327/200) 4096 1907)/2)
    have hp : cPayment 1906 = (71354718396:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1906+point (1327/200) 4096 1907)/2 = (5286251:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1906
  · change cPayment 1907 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1907+point (1327/200) 4096 1908)/2)
    have hp : cPayment 1907 = (71328479934:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1907+point (1327/200) 4096 1908)/2 = (1057461:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1907
  · change cPayment 1908 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1908+point (1327/200) 4096 1909)/2)
    have hp : cPayment 1908 = (71302223006:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1908+point (1327/200) 4096 1909)/2 = (5288359:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1908
  · change cPayment 1909 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1909+point (1327/200) 4096 1910)/2)
    have hp : cPayment 1909 = (71275947644:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1909+point (1327/200) 4096 1910)/2 = (5289413:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1909
  · change cPayment 1910 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1910+point (1327/200) 4096 1911)/2)
    have hp : cPayment 1910 = (71249653881:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1910+point (1327/200) 4096 1911)/2 = (5290467:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1910
  · change cPayment 1911 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1911+point (1327/200) 4096 1912)/2)
    have hp : cPayment 1911 = (71223341746:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1911+point (1327/200) 4096 1912)/2 = (5291521:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1911
  · change cPayment 1912 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1912+point (1327/200) 4096 1913)/2)
    have hp : cPayment 1912 = (71197011273:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1912+point (1327/200) 4096 1913)/2 = (211703:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1912
  · change cPayment 1913 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1913+point (1327/200) 4096 1914)/2)
    have hp : cPayment 1913 = (71170662491:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1913+point (1327/200) 4096 1914)/2 = (5293629:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1913
  · change cPayment 1914 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1914+point (1327/200) 4096 1915)/2)
    have hp : cPayment 1914 = (71144295434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1914+point (1327/200) 4096 1915)/2 = (5294683:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1914
  · change cPayment 1915 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1915+point (1327/200) 4096 1916)/2)
    have hp : cPayment 1915 = (71117910131:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1915+point (1327/200) 4096 1916)/2 = (5295737:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1915
  · change cPayment 1916 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1916+point (1327/200) 4096 1917)/2)
    have hp : cPayment 1916 = (71091506614:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1916+point (1327/200) 4096 1917)/2 = (5296791:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1916
  · change cPayment 1917 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1917+point (1327/200) 4096 1918)/2)
    have hp : cPayment 1917 = (71065084915:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1917+point (1327/200) 4096 1918)/2 = (1059569:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1917
  · change cPayment 1918 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1918+point (1327/200) 4096 1919)/2)
    have hp : cPayment 1918 = (71038645064:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1918+point (1327/200) 4096 1919)/2 = (5298899:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1918
  · change cPayment 1919 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1919+point (1327/200) 4096 1920)/2)
    have hp : cPayment 1919 = (71012187094:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1919+point (1327/200) 4096 1920)/2 = (5299953:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1919
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_119
