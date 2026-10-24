import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints157
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_157 (j : Fin 16) : upperPayment (16*157+j.val) ≤
    upperValue ((point split endpoint 4096 (16*157+j.val)+point split endpoint 4096 (16*157+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2512 ≤ upperValue ((point split endpoint 4096 2512+point split endpoint 4096 2513)/2)
    have hp : upperPayment 2512 = (219972863381:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2512+point split endpoint 4096 2513)/2 = (639340927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639340927:ℝ)/168755200)*ClassicalSixthBranch.v ((639340927:ℝ)/168755200)/ClassicalSixthBranch.r = (103987963186065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2512
  · change upperPayment 2513 ≤ upperValue ((point split endpoint 4096 2513+point split endpoint 4096 2514)/2)
    have hp : upperPayment 2513 = (219860166670:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2513+point split endpoint 4096 2514)/2 = (639366077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639366077:ℝ)/168755200)*ClassicalSixthBranch.v ((639366077:ℝ)/168755200)/ClassicalSixthBranch.r = (103967032362137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2513
  · change upperPayment 2514 ≤ upperValue ((point split endpoint 4096 2514+point split endpoint 4096 2515)/2)
    have hp : upperPayment 2514 = (219747440789:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2514+point split endpoint 4096 2515)/2 = (639391227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639391227:ℝ)/168755200)*ClassicalSixthBranch.v ((639391227:ℝ)/168755200)/ClassicalSixthBranch.r = (103946103562281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2514
  · change upperPayment 2515 ≤ upperValue ((point split endpoint 4096 2515+point split endpoint 4096 2516)/2)
    have hp : upperPayment 2515 = (219634685732:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2515+point split endpoint 4096 2516)/2 = (639416377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639416377:ℝ)/168755200)*ClassicalSixthBranch.v ((639416377:ℝ)/168755200)/ClassicalSixthBranch.r = (103925176786497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2515
  · change upperPayment 2516 ≤ upperValue ((point split endpoint 4096 2516+point split endpoint 4096 2517)/2)
    have hp : upperPayment 2516 = (219521901494:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2516+point split endpoint 4096 2517)/2 = (639441527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639441527:ℝ)/168755200)*ClassicalSixthBranch.v ((639441527:ℝ)/168755200)/ClassicalSixthBranch.r = (103904252034785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2516
  · change upperPayment 2517 ≤ upperValue ((point split endpoint 4096 2517+point split endpoint 4096 2518)/2)
    have hp : upperPayment 2517 = (219409088067:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2517+point split endpoint 4096 2518)/2 = (639466677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639466677:ℝ)/168755200)*ClassicalSixthBranch.v ((639466677:ℝ)/168755200)/ClassicalSixthBranch.r = (103883329307145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2517
  · change upperPayment 2518 ≤ upperValue ((point split endpoint 4096 2518+point split endpoint 4096 2519)/2)
    have hp : upperPayment 2518 = (219296245445:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2518+point split endpoint 4096 2519)/2 = (639491827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639491827:ℝ)/168755200)*ClassicalSixthBranch.v ((639491827:ℝ)/168755200)/ClassicalSixthBranch.r = (103862408603577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2518
  · change upperPayment 2519 ≤ upperValue ((point split endpoint 4096 2519+point split endpoint 4096 2520)/2)
    have hp : upperPayment 2519 = (219183373622:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2519+point split endpoint 4096 2520)/2 = (639516977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639516977:ℝ)/168755200)*ClassicalSixthBranch.v ((639516977:ℝ)/168755200)/ClassicalSixthBranch.r = (103841489924081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2519
  · change upperPayment 2520 ≤ upperValue ((point split endpoint 4096 2520+point split endpoint 4096 2521)/2)
    have hp : upperPayment 2520 = (219070472591:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2520+point split endpoint 4096 2521)/2 = (639542127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639542127:ℝ)/168755200)*ClassicalSixthBranch.v ((639542127:ℝ)/168755200)/ClassicalSixthBranch.r = (103820573268657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2520
  · change upperPayment 2521 ≤ upperValue ((point split endpoint 4096 2521+point split endpoint 4096 2522)/2)
    have hp : upperPayment 2521 = (218957542346:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2521+point split endpoint 4096 2522)/2 = (639567277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639567277:ℝ)/168755200)*ClassicalSixthBranch.v ((639567277:ℝ)/168755200)/ClassicalSixthBranch.r = (103799658637305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2521
  · change upperPayment 2522 ≤ upperValue ((point split endpoint 4096 2522+point split endpoint 4096 2523)/2)
    have hp : upperPayment 2522 = (218844582881:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2522+point split endpoint 4096 2523)/2 = (639592427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639592427:ℝ)/168755200)*ClassicalSixthBranch.v ((639592427:ℝ)/168755200)/ClassicalSixthBranch.r = (103778746030025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2522
  · change upperPayment 2523 ≤ upperValue ((point split endpoint 4096 2523+point split endpoint 4096 2524)/2)
    have hp : upperPayment 2523 = (218731594190:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2523+point split endpoint 4096 2524)/2 = (639617577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639617577:ℝ)/168755200)*ClassicalSixthBranch.v ((639617577:ℝ)/168755200)/ClassicalSixthBranch.r = (103757835446817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2523
  · change upperPayment 2524 ≤ upperValue ((point split endpoint 4096 2524+point split endpoint 4096 2525)/2)
    have hp : upperPayment 2524 = (218618576265:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2524+point split endpoint 4096 2525)/2 = (639642727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639642727:ℝ)/168755200)*ClassicalSixthBranch.v ((639642727:ℝ)/168755200)/ClassicalSixthBranch.r = (103736926887681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2524
  · change upperPayment 2525 ≤ upperValue ((point split endpoint 4096 2525+point split endpoint 4096 2526)/2)
    have hp : upperPayment 2525 = (218505529100:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2525+point split endpoint 4096 2526)/2 = (639667877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639667877:ℝ)/168755200)*ClassicalSixthBranch.v ((639667877:ℝ)/168755200)/ClassicalSixthBranch.r = (103716020352617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2525
  · change upperPayment 2526 ≤ upperValue ((point split endpoint 4096 2526+point split endpoint 4096 2527)/2)
    have hp : upperPayment 2526 = (218392452690:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2526+point split endpoint 4096 2527)/2 = (639693027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639693027:ℝ)/168755200)*ClassicalSixthBranch.v ((639693027:ℝ)/168755200)/ClassicalSixthBranch.r = (103695115841625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2526
  · change upperPayment 2527 ≤ upperValue ((point split endpoint 4096 2527+point split endpoint 4096 2528)/2)
    have hp : upperPayment 2527 = (218279347027:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2527+point split endpoint 4096 2528)/2 = (639718177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639718177:ℝ)/168755200)*ClassicalSixthBranch.v ((639718177:ℝ)/168755200)/ClassicalSixthBranch.r = (103674213354705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2527
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_157
