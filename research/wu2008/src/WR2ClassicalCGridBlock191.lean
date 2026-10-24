import WR2ClassicalCPayments
import WR2ClassicalCPoints191
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_191 (j : Fin 16) : cPayment (16*191+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*191+j.val)+point (1327/200) 4096 (16*191+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3056 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3056+point (1327/200) 4096 3057)/2)
    have hp : cPayment 3056 = (34630866741:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3056+point (1327/200) 4096 3057)/2 = (6498351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3056
  · change cPayment 3057 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3057+point (1327/200) 4096 3058)/2)
    have hp : cPayment 3057 = (34596646601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3057+point (1327/200) 4096 3058)/2 = (1299881:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3057
  · change cPayment 3058 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3058+point (1327/200) 4096 3059)/2)
    have hp : cPayment 3058 = (34562426505:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3058+point (1327/200) 4096 3059)/2 = (6500459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3058
  · change cPayment 3059 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3059+point (1327/200) 4096 3060)/2)
    have hp : cPayment 3059 = (34528206458:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3059+point (1327/200) 4096 3060)/2 = (6501513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3059
  · change cPayment 3060 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3060+point (1327/200) 4096 3061)/2)
    have hp : cPayment 3060 = (34493986469:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3060+point (1327/200) 4096 3061)/2 = (6502567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3060
  · change cPayment 3061 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3061+point (1327/200) 4096 3062)/2)
    have hp : cPayment 3061 = (34459766543:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3061+point (1327/200) 4096 3062)/2 = (6503621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3061
  · change cPayment 3062 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3062+point (1327/200) 4096 3063)/2)
    have hp : cPayment 3062 = (34425546688:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3062+point (1327/200) 4096 3063)/2 = (260187:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3062
  · change cPayment 3063 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3063+point (1327/200) 4096 3064)/2)
    have hp : cPayment 3063 = (34391326910:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3063+point (1327/200) 4096 3064)/2 = (6505729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3063
  · change cPayment 3064 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3064+point (1327/200) 4096 3065)/2)
    have hp : cPayment 3064 = (34357107216:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3064+point (1327/200) 4096 3065)/2 = (6506783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3064
  · change cPayment 3065 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3065+point (1327/200) 4096 3066)/2)
    have hp : cPayment 3065 = (34322887613:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3065+point (1327/200) 4096 3066)/2 = (6507837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3065
  · change cPayment 3066 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3066+point (1327/200) 4096 3067)/2)
    have hp : cPayment 3066 = (34288668107:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3066+point (1327/200) 4096 3067)/2 = (6508891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3066
  · change cPayment 3067 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3067+point (1327/200) 4096 3068)/2)
    have hp : cPayment 3067 = (34254448705:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3067+point (1327/200) 4096 3068)/2 = (1301989:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3067
  · change cPayment 3068 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3068+point (1327/200) 4096 3069)/2)
    have hp : cPayment 3068 = (34220229414:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3068+point (1327/200) 4096 3069)/2 = (6510999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3068
  · change cPayment 3069 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3069+point (1327/200) 4096 3070)/2)
    have hp : cPayment 3069 = (34186010241:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3069+point (1327/200) 4096 3070)/2 = (6512053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3069
  · change cPayment 3070 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3070+point (1327/200) 4096 3071)/2)
    have hp : cPayment 3070 = (34151791192:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3070+point (1327/200) 4096 3071)/2 = (6513107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3070
  · change cPayment 3071 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3071+point (1327/200) 4096 3072)/2)
    have hp : cPayment 3071 = (34117572274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3071+point (1327/200) 4096 3072)/2 = (6514161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3071
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_191
