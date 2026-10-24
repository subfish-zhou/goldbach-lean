import WR2ClassicalCPayments
import WR2ClassicalCPoints128
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_128 (j : Fin 16) : cPayment (16*128+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*128+j.val)+point (1327/200) 4096 (16*128+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2048 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2048+point (1327/200) 4096 2049)/2)
    have hp : cPayment 2048 = (67458083404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2048+point (1327/200) 4096 2049)/2 = (5435919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2048
  · change cPayment 2049 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2049+point (1327/200) 4096 2050)/2)
    have hp : cPayment 2049 = (67429519879:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2049+point (1327/200) 4096 2050)/2 = (5436973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2049
  · change cPayment 2050 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2050+point (1327/200) 4096 2051)/2)
    have hp : cPayment 2050 = (67400941969:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2050+point (1327/200) 4096 2051)/2 = (5438027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2050
  · change cPayment 2051 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2051+point (1327/200) 4096 2052)/2)
    have hp : cPayment 2051 = (67372349701:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2051+point (1327/200) 4096 2052)/2 = (5439081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2051
  · change cPayment 2052 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2052+point (1327/200) 4096 2053)/2)
    have hp : cPayment 2052 = (67343743100:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2052+point (1327/200) 4096 2053)/2 = (1088027:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2052
  · change cPayment 2053 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2053+point (1327/200) 4096 2054)/2)
    have hp : cPayment 2053 = (67315122192:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2053+point (1327/200) 4096 2054)/2 = (5441189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2053
  · change cPayment 2054 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2054+point (1327/200) 4096 2055)/2)
    have hp : cPayment 2054 = (67286487003:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2054+point (1327/200) 4096 2055)/2 = (5442243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2054
  · change cPayment 2055 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2055+point (1327/200) 4096 2056)/2)
    have hp : cPayment 2055 = (67257837559:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2055+point (1327/200) 4096 2056)/2 = (5443297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2055
  · change cPayment 2056 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2056+point (1327/200) 4096 2057)/2)
    have hp : cPayment 2056 = (67229173887:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2056+point (1327/200) 4096 2057)/2 = (5444351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2056
  · change cPayment 2057 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2057+point (1327/200) 4096 2058)/2)
    have hp : cPayment 2057 = (67200496010:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2057+point (1327/200) 4096 2058)/2 = (1089081:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2057
  · change cPayment 2058 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2058+point (1327/200) 4096 2059)/2)
    have hp : cPayment 2058 = (67171803957:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2058+point (1327/200) 4096 2059)/2 = (5446459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2058
  · change cPayment 2059 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2059+point (1327/200) 4096 2060)/2)
    have hp : cPayment 2059 = (67143097751:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2059+point (1327/200) 4096 2060)/2 = (5447513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2059
  · change cPayment 2060 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2060+point (1327/200) 4096 2061)/2)
    have hp : cPayment 2060 = (67114377420:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2060+point (1327/200) 4096 2061)/2 = (5448567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2060
  · change cPayment 2061 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2061+point (1327/200) 4096 2062)/2)
    have hp : cPayment 2061 = (67085642988:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2061+point (1327/200) 4096 2062)/2 = (5449621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2061
  · change cPayment 2062 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2062+point (1327/200) 4096 2063)/2)
    have hp : cPayment 2062 = (67056894482:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2062+point (1327/200) 4096 2063)/2 = (218027:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2062
  · change cPayment 2063 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2063+point (1327/200) 4096 2064)/2)
    have hp : cPayment 2063 = (67028131926:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2063+point (1327/200) 4096 2064)/2 = (5451729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2063
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_128
