import WR2ClassicalCPayments
import WR2ClassicalCPoints121
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_121 (j : Fin 16) : cPayment (16*121+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*121+j.val)+point (1327/200) 4096 (16*121+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1936 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1936+point (1327/200) 4096 1937)/2)
    have hp : cPayment 1936 = (70559659190:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1936+point (1327/200) 4096 1937)/2 = (5317871:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1936
  · change cPayment 1937 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1937+point (1327/200) 4096 1938)/2)
    have hp : cPayment 1937 = (70532880336:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1937+point (1327/200) 4096 1938)/2 = (212757:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1937
  · change cPayment 1938 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1938+point (1327/200) 4096 1939)/2)
    have hp : cPayment 1938 = (70506083945:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1938+point (1327/200) 4096 1939)/2 = (5319979:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1938
  · change cPayment 1939 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1939+point (1327/200) 4096 1940)/2)
    have hp : cPayment 1939 = (70479270049:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1939+point (1327/200) 4096 1940)/2 = (5321033:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1939
  · change cPayment 1940 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1940+point (1327/200) 4096 1941)/2)
    have hp : cPayment 1940 = (70452438677:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1940+point (1327/200) 4096 1941)/2 = (5322087:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1940
  · change cPayment 1941 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1941+point (1327/200) 4096 1942)/2)
    have hp : cPayment 1941 = (70425589860:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1941+point (1327/200) 4096 1942)/2 = (5323141:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1941
  · change cPayment 1942 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1942+point (1327/200) 4096 1943)/2)
    have hp : cPayment 1942 = (70398723628:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1942+point (1327/200) 4096 1943)/2 = (1064839:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1942
  · change cPayment 1943 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1943+point (1327/200) 4096 1944)/2)
    have hp : cPayment 1943 = (70371840010:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1943+point (1327/200) 4096 1944)/2 = (5325249:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1943
  · change cPayment 1944 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1944+point (1327/200) 4096 1945)/2)
    have hp : cPayment 1944 = (70344939038:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1944+point (1327/200) 4096 1945)/2 = (5326303:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1944
  · change cPayment 1945 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1945+point (1327/200) 4096 1946)/2)
    have hp : cPayment 1945 = (70318020741:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1945+point (1327/200) 4096 1946)/2 = (5327357:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1945
  · change cPayment 1946 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1946+point (1327/200) 4096 1947)/2)
    have hp : cPayment 1946 = (70291085149:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1946+point (1327/200) 4096 1947)/2 = (5328411:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1946
  · change cPayment 1947 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1947+point (1327/200) 4096 1948)/2)
    have hp : cPayment 1947 = (70264132292:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1947+point (1327/200) 4096 1948)/2 = (1065893:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1947
  · change cPayment 1948 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1948+point (1327/200) 4096 1949)/2)
    have hp : cPayment 1948 = (70237162200:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1948+point (1327/200) 4096 1949)/2 = (5330519:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1948
  · change cPayment 1949 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1949+point (1327/200) 4096 1950)/2)
    have hp : cPayment 1949 = (70210174904:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1949+point (1327/200) 4096 1950)/2 = (5331573:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1949
  · change cPayment 1950 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1950+point (1327/200) 4096 1951)/2)
    have hp : cPayment 1950 = (70183170432:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1950+point (1327/200) 4096 1951)/2 = (5332627:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1950
  · change cPayment 1951 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1951+point (1327/200) 4096 1952)/2)
    have hp : cPayment 1951 = (70156148815:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1951+point (1327/200) 4096 1952)/2 = (5333681:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1951
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_121
