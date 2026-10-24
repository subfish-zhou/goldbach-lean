import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints190
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_190 (j : Fin 16) : upperPayment (16*190+j.val) ≤
    upperValue ((point split endpoint 4096 (16*190+j.val)+point split endpoint 4096 (16*190+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3040 ≤ upperValue ((point split endpoint 4096 3040+point split endpoint 4096 3041)/2)
    have hp : upperPayment 3040 = (156246993830:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3040+point split endpoint 4096 3041)/2 = (652620127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652620127:ℝ)/168755200)*ClassicalSixthBranch.v ((652620127:ℝ)/168755200)/ClassicalSixthBranch.r = (93218093241297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3040
  · change upperPayment 3041 ≤ upperValue ((point split endpoint 4096 3041+point split endpoint 4096 3042)/2)
    have hp : upperPayment 3041 = (156117944757:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3041+point split endpoint 4096 3042)/2 = (652645277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652645277:ℝ)/168755200)*ClassicalSixthBranch.v ((652645277:ℝ)/168755200)/ClassicalSixthBranch.r = (93198231127385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3041
  · change upperPayment 3042 ≤ upperValue ((point split endpoint 4096 3042+point split endpoint 4096 3043)/2)
    have hp : upperPayment 3042 = (155988862773:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3042+point split endpoint 4096 3043)/2 = (652670427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652670427:ℝ)/168755200)*ClassicalSixthBranch.v ((652670427:ℝ)/168755200)/ClassicalSixthBranch.r = (93178371037545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3042
  · change upperPayment 3043 ≤ upperValue ((point split endpoint 4096 3043+point split endpoint 4096 3044)/2)
    have hp : upperPayment 3043 = (155859747870:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3043+point split endpoint 4096 3044)/2 = (652695577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652695577:ℝ)/168755200)*ClassicalSixthBranch.v ((652695577:ℝ)/168755200)/ClassicalSixthBranch.r = (93158512971777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3043
  · change upperPayment 3044 ≤ upperValue ((point split endpoint 4096 3044+point split endpoint 4096 3045)/2)
    have hp : upperPayment 3044 = (155730600040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3044+point split endpoint 4096 3045)/2 = (652720727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652720727:ℝ)/168755200)*ClassicalSixthBranch.v ((652720727:ℝ)/168755200)/ClassicalSixthBranch.r = (93138656930081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3044
  · change upperPayment 3045 ≤ upperValue ((point split endpoint 4096 3045+point split endpoint 4096 3046)/2)
    have hp : upperPayment 3045 = (155601419275:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3045+point split endpoint 4096 3046)/2 = (652745877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652745877:ℝ)/168755200)*ClassicalSixthBranch.v ((652745877:ℝ)/168755200)/ClassicalSixthBranch.r = (93118802912457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3045
  · change upperPayment 3046 ≤ upperValue ((point split endpoint 4096 3046+point split endpoint 4096 3047)/2)
    have hp : upperPayment 3046 = (155472205567:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3046+point split endpoint 4096 3047)/2 = (652771027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652771027:ℝ)/168755200)*ClassicalSixthBranch.v ((652771027:ℝ)/168755200)/ClassicalSixthBranch.r = (93098950918905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3046
  · change upperPayment 3047 ≤ upperValue ((point split endpoint 4096 3047+point split endpoint 4096 3048)/2)
    have hp : upperPayment 3047 = (155342958909:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3047+point split endpoint 4096 3048)/2 = (652796177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652796177:ℝ)/168755200)*ClassicalSixthBranch.v ((652796177:ℝ)/168755200)/ClassicalSixthBranch.r = (93079100949425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3047
  · change upperPayment 3048 ≤ upperValue ((point split endpoint 4096 3048+point split endpoint 4096 3049)/2)
    have hp : upperPayment 3048 = (155213679292:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3048+point split endpoint 4096 3049)/2 = (652821327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652821327:ℝ)/168755200)*ClassicalSixthBranch.v ((652821327:ℝ)/168755200)/ClassicalSixthBranch.r = (93059253004017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3048
  · change upperPayment 3049 ≤ upperValue ((point split endpoint 4096 3049+point split endpoint 4096 3050)/2)
    have hp : upperPayment 3049 = (155084366709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3049+point split endpoint 4096 3050)/2 = (652846477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652846477:ℝ)/168755200)*ClassicalSixthBranch.v ((652846477:ℝ)/168755200)/ClassicalSixthBranch.r = (93039407082681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3049
  · change upperPayment 3050 ≤ upperValue ((point split endpoint 4096 3050+point split endpoint 4096 3051)/2)
    have hp : upperPayment 3050 = (154955021152:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3050+point split endpoint 4096 3051)/2 = (652871627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652871627:ℝ)/168755200)*ClassicalSixthBranch.v ((652871627:ℝ)/168755200)/ClassicalSixthBranch.r = (93019563185417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3050
  · change upperPayment 3051 ≤ upperValue ((point split endpoint 4096 3051+point split endpoint 4096 3052)/2)
    have hp : upperPayment 3051 = (154825642613:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3051+point split endpoint 4096 3052)/2 = (652896777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652896777:ℝ)/168755200)*ClassicalSixthBranch.v ((652896777:ℝ)/168755200)/ClassicalSixthBranch.r = (92999721312225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3051
  · change upperPayment 3052 ≤ upperValue ((point split endpoint 4096 3052+point split endpoint 4096 3053)/2)
    have hp : upperPayment 3052 = (154696231083:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3052+point split endpoint 4096 3053)/2 = (652921927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652921927:ℝ)/168755200)*ClassicalSixthBranch.v ((652921927:ℝ)/168755200)/ClassicalSixthBranch.r = (92979881463105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3052
  · change upperPayment 3053 ≤ upperValue ((point split endpoint 4096 3053+point split endpoint 4096 3054)/2)
    have hp : upperPayment 3053 = (154566786556:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3053+point split endpoint 4096 3054)/2 = (652947077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652947077:ℝ)/168755200)*ClassicalSixthBranch.v ((652947077:ℝ)/168755200)/ClassicalSixthBranch.r = (92960043638057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3053
  · change upperPayment 3054 ≤ upperValue ((point split endpoint 4096 3054+point split endpoint 4096 3055)/2)
    have hp : upperPayment 3054 = (154437309023:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3054+point split endpoint 4096 3055)/2 = (652972227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652972227:ℝ)/168755200)*ClassicalSixthBranch.v ((652972227:ℝ)/168755200)/ClassicalSixthBranch.r = (92940207837081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3054
  · change upperPayment 3055 ≤ upperValue ((point split endpoint 4096 3055+point split endpoint 4096 3056)/2)
    have hp : upperPayment 3055 = (154307798476:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3055+point split endpoint 4096 3056)/2 = (652997377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652997377:ℝ)/168755200)*ClassicalSixthBranch.v ((652997377:ℝ)/168755200)/ClassicalSixthBranch.r = (92920374060177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3055
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_190
