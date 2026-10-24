import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints175
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_175 (j : Fin 16) : upperPayment (16*175+j.val) ≤
    upperValue ((point split endpoint 4096 (16*175+j.val)+point split endpoint 4096 (16*175+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2800 ≤ upperValue ((point split endpoint 4096 2800+point split endpoint 4096 2801)/2)
    have hp : upperPayment 2800 = (186284899985:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2800+point split endpoint 4096 2801)/2 = (646584127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646584127:ℝ)/168755200)*ClassicalSixthBranch.v ((646584127:ℝ)/168755200)/ClassicalSixthBranch.r = (98043536742417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2800
  · change upperPayment 2801 ≤ upperValue ((point split endpoint 4096 2801+point split endpoint 4096 2802)/2)
    have hp : upperPayment 2801 = (186163529216:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2801+point split endpoint 4096 2802)/2 = (646609277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646609277:ℝ)/168755200)*ClassicalSixthBranch.v ((646609277:ℝ)/168755200)/ClassicalSixthBranch.r = (98023188851225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2801
  · change upperPayment 2802 ≤ upperValue ((point split endpoint 4096 2802+point split endpoint 4096 2803)/2)
    have hp : upperPayment 2802 = (186042127335:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2802+point split endpoint 4096 2803)/2 = (646634427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646634427:ℝ)/168755200)*ClassicalSixthBranch.v ((646634427:ℝ)/168755200)/ClassicalSixthBranch.r = (98002842984105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2802
  · change upperPayment 2803 ≤ upperValue ((point split endpoint 4096 2803+point split endpoint 4096 2804)/2)
    have hp : upperPayment 2803 = (185920694336:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2803+point split endpoint 4096 2804)/2 = (646659577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646659577:ℝ)/168755200)*ClassicalSixthBranch.v ((646659577:ℝ)/168755200)/ClassicalSixthBranch.r = (97982499141057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2803
  · change upperPayment 2804 ≤ upperValue ((point split endpoint 4096 2804+point split endpoint 4096 2805)/2)
    have hp : upperPayment 2804 = (185799230211:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2804+point split endpoint 4096 2805)/2 = (646684727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646684727:ℝ)/168755200)*ClassicalSixthBranch.v ((646684727:ℝ)/168755200)/ClassicalSixthBranch.r = (97962157322081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2804
  · change upperPayment 2805 ≤ upperValue ((point split endpoint 4096 2805+point split endpoint 4096 2806)/2)
    have hp : upperPayment 2805 = (185677734954:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2805+point split endpoint 4096 2806)/2 = (646709877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646709877:ℝ)/168755200)*ClassicalSixthBranch.v ((646709877:ℝ)/168755200)/ClassicalSixthBranch.r = (97941817527177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2805
  · change upperPayment 2806 ≤ upperValue ((point split endpoint 4096 2806+point split endpoint 4096 2807)/2)
    have hp : upperPayment 2806 = (185556208557:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2806+point split endpoint 4096 2807)/2 = (646735027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646735027:ℝ)/168755200)*ClassicalSixthBranch.v ((646735027:ℝ)/168755200)/ClassicalSixthBranch.r = (97921479756345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2806
  · change upperPayment 2807 ≤ upperValue ((point split endpoint 4096 2807+point split endpoint 4096 2808)/2)
    have hp : upperPayment 2807 = (185434651012:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2807+point split endpoint 4096 2808)/2 = (646760177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646760177:ℝ)/168755200)*ClassicalSixthBranch.v ((646760177:ℝ)/168755200)/ClassicalSixthBranch.r = (97901144009585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2807
  · change upperPayment 2808 ≤ upperValue ((point split endpoint 4096 2808+point split endpoint 4096 2809)/2)
    have hp : upperPayment 2808 = (185313062314:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2808+point split endpoint 4096 2809)/2 = (646785327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646785327:ℝ)/168755200)*ClassicalSixthBranch.v ((646785327:ℝ)/168755200)/ClassicalSixthBranch.r = (950299128999:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2808
  · change upperPayment 2809 ≤ upperValue ((point split endpoint 4096 2809+point split endpoint 4096 2810)/2)
    have hp : upperPayment 2809 = (185191442453:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2809+point split endpoint 4096 2810)/2 = (646810477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646810477:ℝ)/168755200)*ClassicalSixthBranch.v ((646810477:ℝ)/168755200)/ClassicalSixthBranch.r = (97860478588281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2809
  · change upperPayment 2810 ≤ upperValue ((point split endpoint 4096 2810+point split endpoint 4096 2811)/2)
    have hp : upperPayment 2810 = (185069791425:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2810+point split endpoint 4096 2811)/2 = (646835627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646835627:ℝ)/168755200)*ClassicalSixthBranch.v ((646835627:ℝ)/168755200)/ClassicalSixthBranch.r = (97840148913737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2810
  · change upperPayment 2811 ≤ upperValue ((point split endpoint 4096 2811+point split endpoint 4096 2812)/2)
    have hp : upperPayment 2811 = (184948109220:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2811+point split endpoint 4096 2812)/2 = (646860777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646860777:ℝ)/168755200)*ClassicalSixthBranch.v ((646860777:ℝ)/168755200)/ClassicalSixthBranch.r = (97819821263265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2811
  · change upperPayment 2812 ≤ upperValue ((point split endpoint 4096 2812+point split endpoint 4096 2813)/2)
    have hp : upperPayment 2812 = (184826395833:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2812+point split endpoint 4096 2813)/2 = (646885927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646885927:ℝ)/168755200)*ClassicalSixthBranch.v ((646885927:ℝ)/168755200)/ClassicalSixthBranch.r = (97799495636865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2812
  · change upperPayment 2813 ≤ upperValue ((point split endpoint 4096 2813+point split endpoint 4096 2814)/2)
    have hp : upperPayment 2813 = (184704651256:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2813+point split endpoint 4096 2814)/2 = (646911077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646911077:ℝ)/168755200)*ClassicalSixthBranch.v ((646911077:ℝ)/168755200)/ClassicalSixthBranch.r = (97779172034537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2813
  · change upperPayment 2814 ≤ upperValue ((point split endpoint 4096 2814+point split endpoint 4096 2815)/2)
    have hp : upperPayment 2814 = (184582875481:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2814+point split endpoint 4096 2815)/2 = (646936227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646936227:ℝ)/168755200)*ClassicalSixthBranch.v ((646936227:ℝ)/168755200)/ClassicalSixthBranch.r = (97758850456281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2814
  · change upperPayment 2815 ≤ upperValue ((point split endpoint 4096 2815+point split endpoint 4096 2816)/2)
    have hp : upperPayment 2815 = (184461068502:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2815+point split endpoint 4096 2816)/2 = (646961377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646961377:ℝ)/168755200)*ClassicalSixthBranch.v ((646961377:ℝ)/168755200)/ClassicalSixthBranch.r = (97738530902097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2815
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_175
