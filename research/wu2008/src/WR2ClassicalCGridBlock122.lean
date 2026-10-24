import WR2ClassicalCPayments
import WR2ClassicalCPoints122
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_122 (j : Fin 16) : cPayment (16*122+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*122+j.val)+point (1327/200) 4096 (16*122+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1952 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1952+point (1327/200) 4096 1953)/2)
    have hp : cPayment 1952 = (70129110083:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1952+point (1327/200) 4096 1953)/2 = (1066947:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1952
  · change cPayment 1953 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1953+point (1327/200) 4096 1954)/2)
    have hp : cPayment 1953 = (70102054265:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1953+point (1327/200) 4096 1954)/2 = (5335789:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1953
  · change cPayment 1954 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1954+point (1327/200) 4096 1955)/2)
    have hp : cPayment 1954 = (70074981391:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1954+point (1327/200) 4096 1955)/2 = (5336843:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1954
  · change cPayment 1955 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1955+point (1327/200) 4096 1956)/2)
    have hp : cPayment 1955 = (70047891490:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1955+point (1327/200) 4096 1956)/2 = (5337897:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1955
  · change cPayment 1956 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1956+point (1327/200) 4096 1957)/2)
    have hp : cPayment 1956 = (70020784593:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1956+point (1327/200) 4096 1957)/2 = (5338951:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1956
  · change cPayment 1957 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1957+point (1327/200) 4096 1958)/2)
    have hp : cPayment 1957 = (69993660729:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1957+point (1327/200) 4096 1958)/2 = (1068001:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1957
  · change cPayment 1958 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1958+point (1327/200) 4096 1959)/2)
    have hp : cPayment 1958 = (69966519927:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1958+point (1327/200) 4096 1959)/2 = (5341059:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1958
  · change cPayment 1959 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1959+point (1327/200) 4096 1960)/2)
    have hp : cPayment 1959 = (69939362216:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1959+point (1327/200) 4096 1960)/2 = (5342113:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1959
  · change cPayment 1960 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1960+point (1327/200) 4096 1961)/2)
    have hp : cPayment 1960 = (69912187628:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1960+point (1327/200) 4096 1961)/2 = (5343167:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1960
  · change cPayment 1961 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1961+point (1327/200) 4096 1962)/2)
    have hp : cPayment 1961 = (69884996189:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1961+point (1327/200) 4096 1962)/2 = (5344221:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1961
  · change cPayment 1962 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1962+point (1327/200) 4096 1963)/2)
    have hp : cPayment 1962 = (69857787932:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1962+point (1327/200) 4096 1963)/2 = (213811:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1962
  · change cPayment 1963 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1963+point (1327/200) 4096 1964)/2)
    have hp : cPayment 1963 = (69830562883:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1963+point (1327/200) 4096 1964)/2 = (5346329:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1963
  · change cPayment 1964 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1964+point (1327/200) 4096 1965)/2)
    have hp : cPayment 1964 = (69803321074:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1964+point (1327/200) 4096 1965)/2 = (5347383:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1964
  · change cPayment 1965 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1965+point (1327/200) 4096 1966)/2)
    have hp : cPayment 1965 = (69776062532:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1965+point (1327/200) 4096 1966)/2 = (5348437:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1965
  · change cPayment 1966 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1966+point (1327/200) 4096 1967)/2)
    have hp : cPayment 1966 = (69748787288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1966+point (1327/200) 4096 1967)/2 = (5349491:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1966
  · change cPayment 1967 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1967+point (1327/200) 4096 1968)/2)
    have hp : cPayment 1967 = (69721495370:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1967+point (1327/200) 4096 1968)/2 = (1070109:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1967
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_122
