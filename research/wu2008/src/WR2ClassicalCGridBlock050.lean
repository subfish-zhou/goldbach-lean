import WR2ClassicalCPayments
import WR2ClassicalCPoints050
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_050 (j : Fin 16) : cPayment (16*50+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*50+j.val)+point (1327/200) 4096 (16*50+j.val+1))/2) := by
  fin_cases j
  · change cPayment 800 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 800+point (1327/200) 4096 801)/2)
    have hp : cPayment 800 = (77954286962:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 800+point (1327/200) 4096 801)/2 = (4120527:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_800
  · change cPayment 801 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 801+point (1327/200) 4096 802)/2)
    have hp : cPayment 801 = (77983753263:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 801+point (1327/200) 4096 802)/2 = (4121581:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_801
  · change cPayment 802 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 802+point (1327/200) 4096 803)/2)
    have hp : cPayment 802 = (78013114517:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 802+point (1327/200) 4096 803)/2 = (824527:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_802
  · change cPayment 803 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 803+point (1327/200) 4096 804)/2)
    have hp : cPayment 803 = (78042370886:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 803+point (1327/200) 4096 804)/2 = (4123689:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_803
  · change cPayment 804 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 804+point (1327/200) 4096 805)/2)
    have hp : cPayment 804 = (78071522535:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 804+point (1327/200) 4096 805)/2 = (4124743:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_804
  · change cPayment 805 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 805+point (1327/200) 4096 806)/2)
    have hp : cPayment 805 = (78100569627:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 805+point (1327/200) 4096 806)/2 = (4125797:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_805
  · change cPayment 806 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 806+point (1327/200) 4096 807)/2)
    have hp : cPayment 806 = (78129512323:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 806+point (1327/200) 4096 807)/2 = (4126851:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_806
  · change cPayment 807 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 807+point (1327/200) 4096 808)/2)
    have hp : cPayment 807 = (78158350786:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 807+point (1327/200) 4096 808)/2 = (825581:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_807
  · change cPayment 808 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 808+point (1327/200) 4096 809)/2)
    have hp : cPayment 808 = (78187085178:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 808+point (1327/200) 4096 809)/2 = (4128959:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_808
  · change cPayment 809 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 809+point (1327/200) 4096 810)/2)
    have hp : cPayment 809 = (78215715660:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 809+point (1327/200) 4096 810)/2 = (4130013:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_809
  · change cPayment 810 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 810+point (1327/200) 4096 811)/2)
    have hp : cPayment 810 = (78244242395:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 810+point (1327/200) 4096 811)/2 = (4131067:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_810
  · change cPayment 811 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 811+point (1327/200) 4096 812)/2)
    have hp : cPayment 811 = (78272665544:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 811+point (1327/200) 4096 812)/2 = (4132121:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_811
  · change cPayment 812 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 812+point (1327/200) 4096 813)/2)
    have hp : cPayment 812 = (78300985267:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 812+point (1327/200) 4096 813)/2 = (165327:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_812
  · change cPayment 813 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 813+point (1327/200) 4096 814)/2)
    have hp : cPayment 813 = (78329201726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 813+point (1327/200) 4096 814)/2 = (4134229:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_813
  · change cPayment 814 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 814+point (1327/200) 4096 815)/2)
    have hp : cPayment 814 = (78357315080:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 814+point (1327/200) 4096 815)/2 = (4135283:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_814
  · change cPayment 815 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 815+point (1327/200) 4096 816)/2)
    have hp : cPayment 815 = (78385325490:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 815+point (1327/200) 4096 816)/2 = (4136337:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_815
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_050
