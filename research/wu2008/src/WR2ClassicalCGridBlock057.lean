import WR2ClassicalCPayments
import WR2ClassicalCPoints057
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_057 (j : Fin 16) : cPayment (16*57+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*57+j.val)+point (1327/200) 4096 (16*57+j.val+1))/2) := by
  fin_cases j
  · change cPayment 912 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 912+point (1327/200) 4096 913)/2)
    have hp : cPayment 912 = (80637169442:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 912+point (1327/200) 4096 913)/2 = (169543:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_912
  · change cPayment 913 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 913+point (1327/200) 4096 914)/2)
    have hp : cPayment 913 = (80655827653:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 913+point (1327/200) 4096 914)/2 = (4239629:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_913
  · change cPayment 914 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 914+point (1327/200) 4096 915)/2)
    have hp : cPayment 914 = (80674397550:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 914+point (1327/200) 4096 915)/2 = (4240683:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_914
  · change cPayment 915 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 915+point (1327/200) 4096 916)/2)
    have hp : cPayment 915 = (80692879270:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 915+point (1327/200) 4096 916)/2 = (4241737:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_915
  · change cPayment 916 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 916+point (1327/200) 4096 917)/2)
    have hp : cPayment 916 = (80711272949:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 916+point (1327/200) 4096 917)/2 = (4242791:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_916
  · change cPayment 917 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 917+point (1327/200) 4096 918)/2)
    have hp : cPayment 917 = (80729578722:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 917+point (1327/200) 4096 918)/2 = (848769:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_917
  · change cPayment 918 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 918+point (1327/200) 4096 919)/2)
    have hp : cPayment 918 = (80747796726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 918+point (1327/200) 4096 919)/2 = (4244899:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_918
  · change cPayment 919 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 919+point (1327/200) 4096 920)/2)
    have hp : cPayment 919 = (80765927094:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 919+point (1327/200) 4096 920)/2 = (4245953:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_919
  · change cPayment 920 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 920+point (1327/200) 4096 921)/2)
    have hp : cPayment 920 = (80783969963:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 920+point (1327/200) 4096 921)/2 = (4247007:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_920
  · change cPayment 921 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 921+point (1327/200) 4096 922)/2)
    have hp : cPayment 921 = (80801925467:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 921+point (1327/200) 4096 922)/2 = (4248061:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_921
  · change cPayment 922 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 922+point (1327/200) 4096 923)/2)
    have hp : cPayment 922 = (80819793740:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 922+point (1327/200) 4096 923)/2 = (849823:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_922
  · change cPayment 923 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 923+point (1327/200) 4096 924)/2)
    have hp : cPayment 923 = (80837574918:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 923+point (1327/200) 4096 924)/2 = (4250169:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_923
  · change cPayment 924 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 924+point (1327/200) 4096 925)/2)
    have hp : cPayment 924 = (80855269134:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 924+point (1327/200) 4096 925)/2 = (4251223:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_924
  · change cPayment 925 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 925+point (1327/200) 4096 926)/2)
    have hp : cPayment 925 = (80872876522:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 925+point (1327/200) 4096 926)/2 = (4252277:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_925
  · change cPayment 926 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 926+point (1327/200) 4096 927)/2)
    have hp : cPayment 926 = (80890397217:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 926+point (1327/200) 4096 927)/2 = (4253331:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_926
  · change cPayment 927 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 927+point (1327/200) 4096 928)/2)
    have hp : cPayment 927 = (80907831351:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 927+point (1327/200) 4096 928)/2 = (850877:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_927
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_057
