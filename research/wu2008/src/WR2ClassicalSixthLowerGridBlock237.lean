import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints237
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_237 (j : Fin 16) : lowerPayment (16*237+j.val) ≤
    lowerValue ((point 2 split 4096 (16*237+j.val)+point 2 split 4096 (16*237+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3792 ≤ lowerValue ((point 2 split 4096 3792+point 2 split 4096 3793)/2)
    have hp : lowerPayment 3792 = (394058628483:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3792+point 2 split 4096 3793)/2 = (111693807:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111693807:ℝ)/33751040)/ClassicalSixthBranch.v ((111693807:ℝ)/33751040) = (520803068059:ℝ)/238508544408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3792
  · change lowerPayment 3793 ≤ lowerValue ((point 2 split 4096 3793+point 2 split 4096 3794)/2)
    have hp : lowerPayment 3793 = (394155480742:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3793+point 2 split 4096 3794)/2 = (558527297:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558527297:ℝ)/168755200)/ClassicalSixthBranch.v ((558527297:ℝ)/168755200) = (104145150877:ℝ)/47692107304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3793
  · change lowerPayment 3794 ≤ lowerValue ((point 2 split 4096 3794+point 2 split 4096 3795)/2)
    have hp : lowerPayment 3794 = (394252349779:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3794+point 2 split 4096 3795)/2 = (558585559:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558585559:ℝ)/168755200)/ClassicalSixthBranch.v ((558585559:ℝ)/168755200) = (520648440711:ℝ)/238412528632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3794
  · change lowerPayment 3795 ≤ lowerValue ((point 2 split 4096 3795+point 2 split 4096 3796)/2)
    have hp : lowerPayment 3795 = (394349235611:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3795+point 2 split 4096 3796)/2 = (558643821:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558643821:ℝ)/168755200)/ClassicalSixthBranch.v ((558643821:ℝ)/168755200) = (520571127037:ℝ)/238364520744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3795
  · change lowerPayment 3796 ≤ lowerValue ((point 2 split 4096 3796+point 2 split 4096 3797)/2)
    have hp : lowerPayment 3796 = (394446138254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3796+point 2 split 4096 3797)/2 = (558702083:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558702083:ℝ)/168755200)/ClassicalSixthBranch.v ((558702083:ℝ)/168755200) = (520493813363:ℝ)/238316512856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3796
  · change lowerPayment 3797 ≤ lowerValue ((point 2 split 4096 3797+point 2 split 4096 3798)/2)
    have hp : lowerPayment 3797 = (394543057727:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3797+point 2 split 4096 3798)/2 = (111752069:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111752069:ℝ)/33751040)/ClassicalSixthBranch.v ((111752069:ℝ)/33751040) = (520416499689:ℝ)/238268504968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3797
  · change lowerPayment 3798 ≤ lowerValue ((point 2 split 4096 3798+point 2 split 4096 3799)/2)
    have hp : lowerPayment 3798 = (394639994046:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3798+point 2 split 4096 3799)/2 = (558818607:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558818607:ℝ)/168755200)/ClassicalSixthBranch.v ((558818607:ℝ)/168755200) = (104067837203:ℝ)/47644099416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3798
  · change lowerPayment 3799 ≤ lowerValue ((point 2 split 4096 3799+point 2 split 4096 3800)/2)
    have hp : lowerPayment 3799 = (394736947229:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3799+point 2 split 4096 3800)/2 = (558876869:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558876869:ℝ)/168755200)/ClassicalSixthBranch.v ((558876869:ℝ)/168755200) = (520261872341:ℝ)/238172489192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3799
  · change lowerPayment 3800 ≤ lowerValue ((point 2 split 4096 3800+point 2 split 4096 3801)/2)
    have hp : lowerPayment 3800 = (394833917293:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3800+point 2 split 4096 3801)/2 = (558935131:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558935131:ℝ)/168755200)/ClassicalSixthBranch.v ((558935131:ℝ)/168755200) = (520184558667:ℝ)/238124481304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3800
  · change lowerPayment 3801 ≤ lowerValue ((point 2 split 4096 3801+point 2 split 4096 3802)/2)
    have hp : lowerPayment 3801 = (394930904255:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3801+point 2 split 4096 3802)/2 = (558993393:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558993393:ℝ)/168755200)/ClassicalSixthBranch.v ((558993393:ℝ)/168755200) = (520107244993:ℝ)/238076473416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3801
  · change lowerPayment 3802 ≤ lowerValue ((point 2 split 4096 3802+point 2 split 4096 3803)/2)
    have hp : lowerPayment 3802 = (395027908132:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3802+point 2 split 4096 3803)/2 = (111810331:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111810331:ℝ)/33751040)/ClassicalSixthBranch.v ((111810331:ℝ)/33751040) = (520029931319:ℝ)/238028465528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3802
  · change lowerPayment 3803 ≤ lowerValue ((point 2 split 4096 3803+point 2 split 4096 3804)/2)
    have hp : lowerPayment 3803 = (395124928942:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3803+point 2 split 4096 3804)/2 = (559109917:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559109917:ℝ)/168755200)/ClassicalSixthBranch.v ((559109917:ℝ)/168755200) = (103990523529:ℝ)/47596091528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3803
  · change lowerPayment 3804 ≤ lowerValue ((point 2 split 4096 3804+point 2 split 4096 3805)/2)
    have hp : lowerPayment 3804 = (395221966702:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3804+point 2 split 4096 3805)/2 = (559168179:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559168179:ℝ)/168755200)/ClassicalSixthBranch.v ((559168179:ℝ)/168755200) = (519875303971:ℝ)/237932449752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3804
  · change lowerPayment 3805 ≤ lowerValue ((point 2 split 4096 3805+point 2 split 4096 3806)/2)
    have hp : lowerPayment 3805 = (395319021430:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3805+point 2 split 4096 3806)/2 = (559226441:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559226441:ℝ)/168755200)/ClassicalSixthBranch.v ((559226441:ℝ)/168755200) = (519797990297:ℝ)/237884441864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3805
  · change lowerPayment 3806 ≤ lowerValue ((point 2 split 4096 3806+point 2 split 4096 3807)/2)
    have hp : lowerPayment 3806 = (395416093142:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3806+point 2 split 4096 3807)/2 = (559284703:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559284703:ℝ)/168755200)/ClassicalSixthBranch.v ((559284703:ℝ)/168755200) = (519720676623:ℝ)/237836433976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3806
  · change lowerPayment 3807 ≤ lowerValue ((point 2 split 4096 3807+point 2 split 4096 3808)/2)
    have hp : lowerPayment 3807 = (395513181855:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3807+point 2 split 4096 3808)/2 = (111868593:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111868593:ℝ)/33751040)/ClassicalSixthBranch.v ((111868593:ℝ)/33751040) = (519643362949:ℝ)/237788426088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3807
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_237
