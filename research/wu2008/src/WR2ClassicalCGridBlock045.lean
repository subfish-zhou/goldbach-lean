import WR2ClassicalCPayments
import WR2ClassicalCPoints045
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_045 (j : Fin 16) : cPayment (16*45+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*45+j.val)+point (1327/200) 4096 (16*45+j.val+1))/2) := by
  fin_cases j
  · change cPayment 720 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 720+point (1327/200) 4096 721)/2)
    have hp : cPayment 720 = (75241650134:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 720+point (1327/200) 4096 721)/2 = (4036207:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_720
  · change cPayment 721 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 721+point (1327/200) 4096 722)/2)
    have hp : cPayment 721 = (75280074377:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 721+point (1327/200) 4096 722)/2 = (4037261:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_721
  · change cPayment 722 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 722+point (1327/200) 4096 723)/2)
    have hp : cPayment 722 = (75318379582:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 722+point (1327/200) 4096 723)/2 = (807663:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_722
  · change cPayment 723 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 723+point (1327/200) 4096 724)/2)
    have hp : cPayment 723 = (75356565938:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 723+point (1327/200) 4096 724)/2 = (4039369:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_723
  · change cPayment 724 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 724+point (1327/200) 4096 725)/2)
    have hp : cPayment 724 = (75394633628:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 724+point (1327/200) 4096 725)/2 = (4040423:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_724
  · change cPayment 725 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 725+point (1327/200) 4096 726)/2)
    have hp : cPayment 725 = (75432582841:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 725+point (1327/200) 4096 726)/2 = (4041477:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_725
  · change cPayment 726 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 726+point (1327/200) 4096 727)/2)
    have hp : cPayment 726 = (75470413761:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 726+point (1327/200) 4096 727)/2 = (4042531:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_726
  · change cPayment 727 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 727+point (1327/200) 4096 728)/2)
    have hp : cPayment 727 = (75508126575:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 727+point (1327/200) 4096 728)/2 = (808717:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_727
  · change cPayment 728 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 728+point (1327/200) 4096 729)/2)
    have hp : cPayment 728 = (75545721466:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 728+point (1327/200) 4096 729)/2 = (4044639:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_728
  · change cPayment 729 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 729+point (1327/200) 4096 730)/2)
    have hp : cPayment 729 = (75583198620:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 729+point (1327/200) 4096 730)/2 = (4045693:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_729
  · change cPayment 730 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 730+point (1327/200) 4096 731)/2)
    have hp : cPayment 730 = (75620558221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 730+point (1327/200) 4096 731)/2 = (4046747:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_730
  · change cPayment 731 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 731+point (1327/200) 4096 732)/2)
    have hp : cPayment 731 = (75657800455:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 731+point (1327/200) 4096 732)/2 = (4047801:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_731
  · change cPayment 732 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 732+point (1327/200) 4096 733)/2)
    have hp : cPayment 732 = (75694925503:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 732+point (1327/200) 4096 733)/2 = (809771:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_732
  · change cPayment 733 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 733+point (1327/200) 4096 734)/2)
    have hp : cPayment 733 = (75731933551:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 733+point (1327/200) 4096 734)/2 = (4049909:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_733
  · change cPayment 734 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 734+point (1327/200) 4096 735)/2)
    have hp : cPayment 734 = (75768824780:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 734+point (1327/200) 4096 735)/2 = (4050963:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_734
  · change cPayment 735 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 735+point (1327/200) 4096 736)/2)
    have hp : cPayment 735 = (75805599376:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 735+point (1327/200) 4096 736)/2 = (4052017:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_735
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_045
