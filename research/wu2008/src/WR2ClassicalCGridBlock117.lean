import WR2ClassicalCPayments
import WR2ClassicalCPoints117
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_117 (j : Fin 16) : cPayment (16*117+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*117+j.val)+point (1327/200) 4096 (16*117+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1872 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1872+point (1327/200) 4096 1873)/2)
    have hp : cPayment 1872 = (72235610821:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1872+point (1327/200) 4096 1873)/2 = (1050083:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1872
  · change cPayment 1873 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1873+point (1327/200) 4096 1874)/2)
    have hp : cPayment 1873 = (72210019288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1873+point (1327/200) 4096 1874)/2 = (5251469:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1873
  · change cPayment 1874 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1874+point (1327/200) 4096 1875)/2)
    have hp : cPayment 1874 = (72184408190:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1874+point (1327/200) 4096 1875)/2 = (5252523:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1874
  · change cPayment 1875 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1875+point (1327/200) 4096 1876)/2)
    have hp : cPayment 1875 = (72158777559:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1875+point (1327/200) 4096 1876)/2 = (5253577:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1875
  · change cPayment 1876 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1876+point (1327/200) 4096 1877)/2)
    have hp : cPayment 1876 = (72133127428:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1876+point (1327/200) 4096 1877)/2 = (5254631:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1876
  · change cPayment 1877 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1877+point (1327/200) 4096 1878)/2)
    have hp : cPayment 1877 = (72107457832:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1877+point (1327/200) 4096 1878)/2 = (1051137:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1877
  · change cPayment 1878 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1878+point (1327/200) 4096 1879)/2)
    have hp : cPayment 1878 = (72081768801:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1878+point (1327/200) 4096 1879)/2 = (5256739:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1878
  · change cPayment 1879 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1879+point (1327/200) 4096 1880)/2)
    have hp : cPayment 1879 = (72056060371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1879+point (1327/200) 4096 1880)/2 = (5257793:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1879
  · change cPayment 1880 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1880+point (1327/200) 4096 1881)/2)
    have hp : cPayment 1880 = (72030332572:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1880+point (1327/200) 4096 1881)/2 = (5258847:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1880
  · change cPayment 1881 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1881+point (1327/200) 4096 1882)/2)
    have hp : cPayment 1881 = (72004585439:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1881+point (1327/200) 4096 1882)/2 = (5259901:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1881
  · change cPayment 1882 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1882+point (1327/200) 4096 1883)/2)
    have hp : cPayment 1882 = (71978819004:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1882+point (1327/200) 4096 1883)/2 = (1052191:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1882
  · change cPayment 1883 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1883+point (1327/200) 4096 1884)/2)
    have hp : cPayment 1883 = (71953033299:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1883+point (1327/200) 4096 1884)/2 = (5262009:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1883
  · change cPayment 1884 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1884+point (1327/200) 4096 1885)/2)
    have hp : cPayment 1884 = (71927228358:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1884+point (1327/200) 4096 1885)/2 = (5263063:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1884
  · change cPayment 1885 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1885+point (1327/200) 4096 1886)/2)
    have hp : cPayment 1885 = (71901404213:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1885+point (1327/200) 4096 1886)/2 = (5264117:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1885
  · change cPayment 1886 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1886+point (1327/200) 4096 1887)/2)
    have hp : cPayment 1886 = (71875560897:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1886+point (1327/200) 4096 1887)/2 = (5265171:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1886
  · change cPayment 1887 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1887+point (1327/200) 4096 1888)/2)
    have hp : cPayment 1887 = (71849698441:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1887+point (1327/200) 4096 1888)/2 = (210649:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1887
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_117
