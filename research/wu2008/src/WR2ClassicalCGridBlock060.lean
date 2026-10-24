import WR2ClassicalCPayments
import WR2ClassicalCPoints060
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_060 (j : Fin 16) : cPayment (16*60+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*60+j.val)+point (1327/200) 4096 (16*60+j.val+1))/2) := by
  fin_cases j
  · change cPayment 960 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 960+point (1327/200) 4096 961)/2)
    have hp : cPayment 960 = (81435459045:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 960+point (1327/200) 4096 961)/2 = (4289167:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_960
  · change cPayment 961 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 961+point (1327/200) 4096 962)/2)
    have hp : cPayment 961 = (81450028085:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 961+point (1327/200) 4096 962)/2 = (4290221:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_961
  · change cPayment 962 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 962+point (1327/200) 4096 963)/2)
    have hp : cPayment 962 = (81464515107:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 962+point (1327/200) 4096 963)/2 = (171651:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_962
  · change cPayment 963 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 963+point (1327/200) 4096 964)/2)
    have hp : cPayment 963 = (81478920237:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 963+point (1327/200) 4096 964)/2 = (4292329:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_963
  · change cPayment 964 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 964+point (1327/200) 4096 965)/2)
    have hp : cPayment 964 = (81493243601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 964+point (1327/200) 4096 965)/2 = (4293383:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_964
  · change cPayment 965 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 965+point (1327/200) 4096 966)/2)
    have hp : cPayment 965 = (81507485324:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 965+point (1327/200) 4096 966)/2 = (4294437:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_965
  · change cPayment 966 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 966+point (1327/200) 4096 967)/2)
    have hp : cPayment 966 = (81521645533:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 966+point (1327/200) 4096 967)/2 = (4295491:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_966
  · change cPayment 967 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 967+point (1327/200) 4096 968)/2)
    have hp : cPayment 967 = (81535724352:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 967+point (1327/200) 4096 968)/2 = (859309:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_967
  · change cPayment 968 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 968+point (1327/200) 4096 969)/2)
    have hp : cPayment 968 = (81549721906:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 968+point (1327/200) 4096 969)/2 = (4297599:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_968
  · change cPayment 969 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 969+point (1327/200) 4096 970)/2)
    have hp : cPayment 969 = (81563638321:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 969+point (1327/200) 4096 970)/2 = (4298653:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_969
  · change cPayment 970 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 970+point (1327/200) 4096 971)/2)
    have hp : cPayment 970 = (81577473721:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 970+point (1327/200) 4096 971)/2 = (4299707:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_970
  · change cPayment 971 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 971+point (1327/200) 4096 972)/2)
    have hp : cPayment 971 = (81591228230:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 971+point (1327/200) 4096 972)/2 = (4300761:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_971
  · change cPayment 972 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 972+point (1327/200) 4096 973)/2)
    have hp : cPayment 972 = (81604901973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 972+point (1327/200) 4096 973)/2 = (860363:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_972
  · change cPayment 973 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 973+point (1327/200) 4096 974)/2)
    have hp : cPayment 973 = (81618495075:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 973+point (1327/200) 4096 974)/2 = (4302869:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_973
  · change cPayment 974 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 974+point (1327/200) 4096 975)/2)
    have hp : cPayment 974 = (81632007658:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 974+point (1327/200) 4096 975)/2 = (4303923:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_974
  · change cPayment 975 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 975+point (1327/200) 4096 976)/2)
    have hp : cPayment 975 = (81645439847:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 975+point (1327/200) 4096 976)/2 = (4304977:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_975
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_060
