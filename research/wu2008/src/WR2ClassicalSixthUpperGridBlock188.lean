import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints188
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_188 (j : Fin 16) : upperPayment (16*188+j.val) ≤
    upperValue ((point split endpoint 4096 (16*188+j.val)+point split endpoint 4096 (16*188+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3008 ≤ upperValue ((point split endpoint 4096 3008+point split endpoint 4096 3009)/2)
    have hp : upperPayment 3008 = (160359234012:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3008+point split endpoint 4096 3009)/2 = (651815327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651815327:ℝ)/168755200)*ClassicalSixthBranch.v ((651815327:ℝ)/168755200)/ClassicalSixthBranch.r = (93854749596497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3008
  · change upperPayment 3009 ≤ upperValue ((point split endpoint 4096 3009+point split endpoint 4096 3010)/2)
    have hp : upperPayment 3009 = (160231233959:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3009+point split endpoint 4096 3010)/2 = (651840477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651840477:ℝ)/168755200)*ClassicalSixthBranch.v ((651840477:ℝ)/168755200)/ClassicalSixthBranch.r = (93834822712281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3009
  · change upperPayment 3010 ≤ upperValue ((point split endpoint 4096 3010+point split endpoint 4096 3011)/2)
    have hp : upperPayment 3010 = (160103201245:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3010+point split endpoint 4096 3011)/2 = (651865627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651865627:ℝ)/168755200)*ClassicalSixthBranch.v ((651865627:ℝ)/168755200)/ClassicalSixthBranch.r = (93814897852137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3010
  · change upperPayment 3011 ≤ upperValue ((point split endpoint 4096 3011+point split endpoint 4096 3012)/2)
    have hp : upperPayment 3011 = (159975135862:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3011+point split endpoint 4096 3012)/2 = (651890777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651890777:ℝ)/168755200)*ClassicalSixthBranch.v ((651890777:ℝ)/168755200)/ClassicalSixthBranch.r = (93794975016065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3011
  · change upperPayment 3012 ≤ upperValue ((point split endpoint 4096 3012+point split endpoint 4096 3013)/2)
    have hp : upperPayment 3012 = (159847037803:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3012+point split endpoint 4096 3013)/2 = (651915927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651915927:ℝ)/168755200)*ClassicalSixthBranch.v ((651915927:ℝ)/168755200)/ClassicalSixthBranch.r = (93775054204065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3012
  · change upperPayment 3013 ≤ upperValue ((point split endpoint 4096 3013+point split endpoint 4096 3014)/2)
    have hp : upperPayment 3013 = (159718907060:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3013+point split endpoint 4096 3014)/2 = (651941077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651941077:ℝ)/168755200)*ClassicalSixthBranch.v ((651941077:ℝ)/168755200)/ClassicalSixthBranch.r = (93755135416137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3013
  · change upperPayment 3014 ≤ upperValue ((point split endpoint 4096 3014+point split endpoint 4096 3015)/2)
    have hp : upperPayment 3014 = (159590743624:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3014+point split endpoint 4096 3015)/2 = (651966227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651966227:ℝ)/168755200)*ClassicalSixthBranch.v ((651966227:ℝ)/168755200)/ClassicalSixthBranch.r = (910050666527:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3014
  · change upperPayment 3015 ≤ upperValue ((point split endpoint 4096 3015+point split endpoint 4096 3016)/2)
    have hp : upperPayment 3015 = (159462547489:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3015+point split endpoint 4096 3016)/2 = (651991377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651991377:ℝ)/168755200)*ClassicalSixthBranch.v ((651991377:ℝ)/168755200)/ClassicalSixthBranch.r = (93715303912497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3015
  · change upperPayment 3016 ≤ upperValue ((point split endpoint 4096 3016+point split endpoint 4096 3017)/2)
    have hp : upperPayment 3016 = (159334318646:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3016+point split endpoint 4096 3017)/2 = (652016527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652016527:ℝ)/168755200)*ClassicalSixthBranch.v ((652016527:ℝ)/168755200)/ClassicalSixthBranch.r = (93695391196785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3016
  · change upperPayment 3017 ≤ upperValue ((point split endpoint 4096 3017+point split endpoint 4096 3018)/2)
    have hp : upperPayment 3017 = (159206057088:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3017+point split endpoint 4096 3018)/2 = (652041677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652041677:ℝ)/168755200)*ClassicalSixthBranch.v ((652041677:ℝ)/168755200)/ClassicalSixthBranch.r = (93675480505145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3017
  · change upperPayment 3018 ≤ upperValue ((point split endpoint 4096 3018+point split endpoint 4096 3019)/2)
    have hp : upperPayment 3018 = (159077762806:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3018+point split endpoint 4096 3019)/2 = (652066827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652066827:ℝ)/168755200)*ClassicalSixthBranch.v ((652066827:ℝ)/168755200)/ClassicalSixthBranch.r = (93655571837577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3018
  · change upperPayment 3019 ≤ upperValue ((point split endpoint 4096 3019+point split endpoint 4096 3020)/2)
    have hp : upperPayment 3019 = (158949435793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3019+point split endpoint 4096 3020)/2 = (652091977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652091977:ℝ)/168755200)*ClassicalSixthBranch.v ((652091977:ℝ)/168755200)/ClassicalSixthBranch.r = (93635665194081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3019
  · change upperPayment 3020 ≤ upperValue ((point split endpoint 4096 3020+point split endpoint 4096 3021)/2)
    have hp : upperPayment 3020 = (158821076042:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3020+point split endpoint 4096 3021)/2 = (652117127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652117127:ℝ)/168755200)*ClassicalSixthBranch.v ((652117127:ℝ)/168755200)/ClassicalSixthBranch.r = (93615760574657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3020
  · change upperPayment 3021 ≤ upperValue ((point split endpoint 4096 3021+point split endpoint 4096 3022)/2)
    have hp : upperPayment 3021 = (158692683544:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3021+point split endpoint 4096 3022)/2 = (652142277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652142277:ℝ)/168755200)*ClassicalSixthBranch.v ((652142277:ℝ)/168755200)/ClassicalSixthBranch.r = (93595857979305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3021
  · change upperPayment 3022 ≤ upperValue ((point split endpoint 4096 3022+point split endpoint 4096 3023)/2)
    have hp : upperPayment 3022 = (158564258292:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3022+point split endpoint 4096 3023)/2 = (652167427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652167427:ℝ)/168755200)*ClassicalSixthBranch.v ((652167427:ℝ)/168755200)/ClassicalSixthBranch.r = (93575957408025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3022
  · change upperPayment 3023 ≤ upperValue ((point split endpoint 4096 3023+point split endpoint 4096 3024)/2)
    have hp : upperPayment 3023 = (158435800277:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3023+point split endpoint 4096 3024)/2 = (652192577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652192577:ℝ)/168755200)*ClassicalSixthBranch.v ((652192577:ℝ)/168755200)/ClassicalSixthBranch.r = (93556058860817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3023
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_188
