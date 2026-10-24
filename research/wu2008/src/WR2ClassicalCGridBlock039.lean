import WR2ClassicalCPayments
import WR2ClassicalCPoints039
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_039 (j : Fin 16) : cPayment (16*39+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*39+j.val)+point (1327/200) 4096 (16*39+j.val+1))/2) := by
  fin_cases j
  · change cPayment 624 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 624+point (1327/200) 4096 625)/2)
    have hp : cPayment 624 = (70969061904:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 624+point (1327/200) 4096 625)/2 = (3935023:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_624
  · change cPayment 625 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 625+point (1327/200) 4096 626)/2)
    have hp : cPayment 625 = (71019833079:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 625+point (1327/200) 4096 626)/2 = (3936077:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_625
  · change cPayment 626 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 626+point (1327/200) 4096 627)/2)
    have hp : cPayment 626 = (71070465735:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 626+point (1327/200) 4096 627)/2 = (3937131:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_626
  · change cPayment 627 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 627+point (1327/200) 4096 628)/2)
    have hp : cPayment 627 = (71120960093:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 627+point (1327/200) 4096 628)/2 = (787637:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_627
  · change cPayment 628 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 628+point (1327/200) 4096 629)/2)
    have hp : cPayment 628 = (71171316370:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 628+point (1327/200) 4096 629)/2 = (3939239:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_628
  · change cPayment 629 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 629+point (1327/200) 4096 630)/2)
    have hp : cPayment 629 = (71221534788:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 629+point (1327/200) 4096 630)/2 = (3940293:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_629
  · change cPayment 630 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 630+point (1327/200) 4096 631)/2)
    have hp : cPayment 630 = (71271615563:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 630+point (1327/200) 4096 631)/2 = (3941347:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_630
  · change cPayment 631 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 631+point (1327/200) 4096 632)/2)
    have hp : cPayment 631 = (71321558916:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 631+point (1327/200) 4096 632)/2 = (3942401:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_631
  · change cPayment 632 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 632+point (1327/200) 4096 633)/2)
    have hp : cPayment 632 = (71371365063:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 632+point (1327/200) 4096 633)/2 = (788691:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_632
  · change cPayment 633 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 633+point (1327/200) 4096 634)/2)
    have hp : cPayment 633 = (71421034222:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 633+point (1327/200) 4096 634)/2 = (3944509:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_633
  · change cPayment 634 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 634+point (1327/200) 4096 635)/2)
    have hp : cPayment 634 = (71470566611:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 634+point (1327/200) 4096 635)/2 = (3945563:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_634
  · change cPayment 635 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 635+point (1327/200) 4096 636)/2)
    have hp : cPayment 635 = (71519962446:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 635+point (1327/200) 4096 636)/2 = (3946617:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_635
  · change cPayment 636 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 636+point (1327/200) 4096 637)/2)
    have hp : cPayment 636 = (71569221944:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 636+point (1327/200) 4096 637)/2 = (3947671:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_636
  · change cPayment 637 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 637+point (1327/200) 4096 638)/2)
    have hp : cPayment 637 = (71618345321:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 637+point (1327/200) 4096 638)/2 = (157949:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_637
  · change cPayment 638 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 638+point (1327/200) 4096 639)/2)
    have hp : cPayment 638 = (71667332794:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 638+point (1327/200) 4096 639)/2 = (3949779:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_638
  · change cPayment 639 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 639+point (1327/200) 4096 640)/2)
    have hp : cPayment 639 = (71716184576:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 639+point (1327/200) 4096 640)/2 = (3950833:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_639
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_039
