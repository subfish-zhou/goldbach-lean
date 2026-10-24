import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints236
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_236 (j : Fin 16) : lowerPayment (16*236+j.val) ≤
    lowerValue ((point 2 split 4096 (16*236+j.val)+point 2 split 4096 (16*236+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3776 ≤ lowerValue ((point 2 split 4096 3776+point 2 split 4096 3777)/2)
    have hp : lowerPayment 3776 = (392511260057:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3776+point 2 split 4096 3777)/2 = (557536843:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557536843:ℝ)/168755200)/ClassicalSixthBranch.v ((557536843:ℝ)/168755200) = (522040086843:ℝ)/239276670616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3776
  · change lowerPayment 3777 ≤ lowerValue ((point 2 split 4096 3777+point 2 split 4096 3778)/2)
    have hp : lowerPayment 3777 = (392607846211:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3777+point 2 split 4096 3778)/2 = (111519021:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111519021:ℝ)/33751040)/ClassicalSixthBranch.v ((111519021:ℝ)/33751040) = (521962773169:ℝ)/239228662728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3777
  · change lowerPayment 3778 ≤ lowerValue ((point 2 split 4096 3778+point 2 split 4096 3779)/2)
    have hp : lowerPayment 3778 = (392704448869:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3778+point 2 split 4096 3779)/2 = (557653367:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557653367:ℝ)/168755200)/ClassicalSixthBranch.v ((557653367:ℝ)/168755200) = (104377091899:ℝ)/47836130968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3778
  · change lowerPayment 3779 ≤ lowerValue ((point 2 split 4096 3779+point 2 split 4096 3780)/2)
    have hp : lowerPayment 3779 = (392801068046:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3779+point 2 split 4096 3780)/2 = (557711629:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557711629:ℝ)/168755200)/ClassicalSixthBranch.v ((557711629:ℝ)/168755200) = (521808145821:ℝ)/239132646952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3779
  · change lowerPayment 3780 ≤ lowerValue ((point 2 split 4096 3780+point 2 split 4096 3781)/2)
    have hp : lowerPayment 3780 = (392897703761:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3780+point 2 split 4096 3781)/2 = (557769891:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557769891:ℝ)/168755200)/ClassicalSixthBranch.v ((557769891:ℝ)/168755200) = (521730832147:ℝ)/239084639064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3780
  · change lowerPayment 3781 ≤ lowerValue ((point 2 split 4096 3781+point 2 split 4096 3782)/2)
    have hp : lowerPayment 3781 = (392994356030:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3781+point 2 split 4096 3782)/2 = (557828153:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557828153:ℝ)/168755200)/ClassicalSixthBranch.v ((557828153:ℝ)/168755200) = (521653518473:ℝ)/239036631176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3781
  · change lowerPayment 3782 ≤ lowerValue ((point 2 split 4096 3782+point 2 split 4096 3783)/2)
    have hp : lowerPayment 3782 = (393091024871:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3782+point 2 split 4096 3783)/2 = (111577283:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111577283:ℝ)/33751040)/ClassicalSixthBranch.v ((111577283:ℝ)/33751040) = (521576204799:ℝ)/238988623288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3782
  · change lowerPayment 3783 ≤ lowerValue ((point 2 split 4096 3783+point 2 split 4096 3784)/2)
    have hp : lowerPayment 3783 = (393187710300:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3783+point 2 split 4096 3784)/2 = (557944677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557944677:ℝ)/168755200)/ClassicalSixthBranch.v ((557944677:ℝ)/168755200) = (20859955645:ℝ)/9557624616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3783
  · change lowerPayment 3784 ≤ lowerValue ((point 2 split 4096 3784+point 2 split 4096 3785)/2)
    have hp : lowerPayment 3784 = (393284412335:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3784+point 2 split 4096 3785)/2 = (558002939:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558002939:ℝ)/168755200)/ClassicalSixthBranch.v ((558002939:ℝ)/168755200) = (521421577451:ℝ)/238892607512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3784
  · change lowerPayment 3785 ≤ lowerValue ((point 2 split 4096 3785+point 2 split 4096 3786)/2)
    have hp : lowerPayment 3785 = (393381130993:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3785+point 2 split 4096 3786)/2 = (558061201:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558061201:ℝ)/168755200)/ClassicalSixthBranch.v ((558061201:ℝ)/168755200) = (521344263777:ℝ)/238844599624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3785
  · change lowerPayment 3786 ≤ lowerValue ((point 2 split 4096 3786+point 2 split 4096 3787)/2)
    have hp : lowerPayment 3786 = (393477866291:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3786+point 2 split 4096 3787)/2 = (558119463:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558119463:ℝ)/168755200)/ClassicalSixthBranch.v ((558119463:ℝ)/168755200) = (521266950103:ℝ)/238796591736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3786
  · change lowerPayment 3787 ≤ lowerValue ((point 2 split 4096 3787+point 2 split 4096 3788)/2)
    have hp : lowerPayment 3787 = (393574618246:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3787+point 2 split 4096 3788)/2 = (22327109:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22327109:ℝ)/6750208)/ClassicalSixthBranch.v ((22327109:ℝ)/6750208) = (521189636429:ℝ)/238748583848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3787
  · change lowerPayment 3788 ≤ lowerValue ((point 2 split 4096 3788+point 2 split 4096 3789)/2)
    have hp : lowerPayment 3788 = (393671386876:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3788+point 2 split 4096 3789)/2 = (558235987:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558235987:ℝ)/168755200)/ClassicalSixthBranch.v ((558235987:ℝ)/168755200) = (104222464551:ℝ)/47740115192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3788
  · change lowerPayment 3789 ≤ lowerValue ((point 2 split 4096 3789+point 2 split 4096 3790)/2)
    have hp : lowerPayment 3789 = (393768172198:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3789+point 2 split 4096 3790)/2 = (558294249:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558294249:ℝ)/168755200)/ClassicalSixthBranch.v ((558294249:ℝ)/168755200) = (521035009081:ℝ)/238652568072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3789
  · change lowerPayment 3790 ≤ lowerValue ((point 2 split 4096 3790+point 2 split 4096 3791)/2)
    have hp : lowerPayment 3790 = (393864974228:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3790+point 2 split 4096 3791)/2 = (558352511:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558352511:ℝ)/168755200)/ClassicalSixthBranch.v ((558352511:ℝ)/168755200) = (520957695407:ℝ)/238604560184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3790
  · change lowerPayment 3791 ≤ lowerValue ((point 2 split 4096 3791+point 2 split 4096 3792)/2)
    have hp : lowerPayment 3791 = (393961792984:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3791+point 2 split 4096 3792)/2 = (558410773:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((558410773:ℝ)/168755200)/ClassicalSixthBranch.v ((558410773:ℝ)/168755200) = (520880381733:ℝ)/238556552296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3791
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_236
