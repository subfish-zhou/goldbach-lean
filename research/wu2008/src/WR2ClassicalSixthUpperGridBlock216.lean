import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints216
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_216 (j : Fin 16) : upperPayment (16*216+j.val) ≤
    upperValue ((point split endpoint 4096 (16*216+j.val)+point split endpoint 4096 (16*216+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3456 ≤ upperValue ((point split endpoint 4096 3456+point split endpoint 4096 3457)/2)
    have hp : upperPayment 3456 = (99623832448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3456+point split endpoint 4096 3457)/2 = (663082527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663082527:ℝ)/168755200)*ClassicalSixthBranch.v ((663082527:ℝ)/168755200)/ClassicalSixthBranch.r = (85130171748945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3456
  · change upperPayment 3457 ≤ upperValue ((point split endpoint 4096 3457+point split endpoint 4096 3458)/2)
    have hp : upperPayment 3457 = (99480372877:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3457+point split endpoint 4096 3458)/2 = (663107677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663107677:ℝ)/168755200)*ClassicalSixthBranch.v ((663107677:ℝ)/168755200)/ClassicalSixthBranch.r = (85111151648985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3457
  · change upperPayment 3458 ≤ upperValue ((point split endpoint 4096 3458+point split endpoint 4096 3459)/2)
    have hp : upperPayment 3458 = (99336876826:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3458+point split endpoint 4096 3459)/2 = (663132827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663132827:ℝ)/168755200)*ClassicalSixthBranch.v ((663132827:ℝ)/168755200)/ClassicalSixthBranch.r = (85092133573097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3458
  · change upperPayment 3459 ≤ upperValue ((point split endpoint 4096 3459+point split endpoint 4096 3460)/2)
    have hp : upperPayment 3459 = (99193344285:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3459+point split endpoint 4096 3460)/2 = (663157977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663157977:ℝ)/168755200)*ClassicalSixthBranch.v ((663157977:ℝ)/168755200)/ClassicalSixthBranch.r = (85073117521281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3459
  · change upperPayment 3460 ≤ upperValue ((point split endpoint 4096 3460+point split endpoint 4096 3461)/2)
    have hp : upperPayment 3460 = (99049775246:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3460+point split endpoint 4096 3461)/2 = (663183127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663183127:ℝ)/168755200)*ClassicalSixthBranch.v ((663183127:ℝ)/168755200)/ClassicalSixthBranch.r = (85054103493537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3460
  · change upperPayment 3461 ≤ upperValue ((point split endpoint 4096 3461+point split endpoint 4096 3462)/2)
    have hp : upperPayment 3461 = (98906169698:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3461+point split endpoint 4096 3462)/2 = (663208277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663208277:ℝ)/168755200)*ClassicalSixthBranch.v ((663208277:ℝ)/168755200)/ClassicalSixthBranch.r = (85035091489865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3461
  · change upperPayment 3462 ≤ upperValue ((point split endpoint 4096 3462+point split endpoint 4096 3463)/2)
    have hp : upperPayment 3462 = (98762527633:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3462+point split endpoint 4096 3463)/2 = (663233427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663233427:ℝ)/168755200)*ClassicalSixthBranch.v ((663233427:ℝ)/168755200)/ClassicalSixthBranch.r = (85016081510265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3462
  · change upperPayment 3463 ≤ upperValue ((point split endpoint 4096 3463+point split endpoint 4096 3464)/2)
    have hp : upperPayment 3463 = (98618849040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3463+point split endpoint 4096 3464)/2 = (663258577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663258577:ℝ)/168755200)*ClassicalSixthBranch.v ((663258577:ℝ)/168755200)/ClassicalSixthBranch.r = (84997073554737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3463
  · change upperPayment 3464 ≤ upperValue ((point split endpoint 4096 3464+point split endpoint 4096 3465)/2)
    have hp : upperPayment 3464 = (98475133912:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3464+point split endpoint 4096 3465)/2 = (663283727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663283727:ℝ)/168755200)*ClassicalSixthBranch.v ((663283727:ℝ)/168755200)/ClassicalSixthBranch.r = (84978067623281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3464
  · change upperPayment 3465 ≤ upperValue ((point split endpoint 4096 3465+point split endpoint 4096 3466)/2)
    have hp : upperPayment 3465 = (98331382237:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3465+point split endpoint 4096 3466)/2 = (663308877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663308877:ℝ)/168755200)*ClassicalSixthBranch.v ((663308877:ℝ)/168755200)/ClassicalSixthBranch.r = (84959063715897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3465
  · change upperPayment 3466 ≤ upperValue ((point split endpoint 4096 3466+point split endpoint 4096 3467)/2)
    have hp : upperPayment 3466 = (98187594008:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3466+point split endpoint 4096 3467)/2 = (663334027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663334027:ℝ)/168755200)*ClassicalSixthBranch.v ((663334027:ℝ)/168755200)/ClassicalSixthBranch.r = (84940061832585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3466
  · change upperPayment 3467 ≤ upperValue ((point split endpoint 4096 3467+point split endpoint 4096 3468)/2)
    have hp : upperPayment 3467 = (98043769215:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3467+point split endpoint 4096 3468)/2 = (663359177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663359177:ℝ)/168755200)*ClassicalSixthBranch.v ((663359177:ℝ)/168755200)/ClassicalSixthBranch.r = (84921061973345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3467
  · change upperPayment 3468 ≤ upperValue ((point split endpoint 4096 3468+point split endpoint 4096 3469)/2)
    have hp : upperPayment 3468 = (97899907847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3468+point split endpoint 4096 3469)/2 = (663384327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663384327:ℝ)/168755200)*ClassicalSixthBranch.v ((663384327:ℝ)/168755200)/ClassicalSixthBranch.r = (84902064138177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3468
  · change upperPayment 3469 ≤ upperValue ((point split endpoint 4096 3469+point split endpoint 4096 3470)/2)
    have hp : upperPayment 3469 = (97756009897:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3469+point split endpoint 4096 3470)/2 = (663409477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663409477:ℝ)/168755200)*ClassicalSixthBranch.v ((663409477:ℝ)/168755200)/ClassicalSixthBranch.r = (84883068327081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3469
  · change upperPayment 3470 ≤ upperValue ((point split endpoint 4096 3470+point split endpoint 4096 3471)/2)
    have hp : upperPayment 3470 = (97612075354:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3470+point split endpoint 4096 3471)/2 = (663434627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663434627:ℝ)/168755200)*ClassicalSixthBranch.v ((663434627:ℝ)/168755200)/ClassicalSixthBranch.r = (84864074540057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3470
  · change upperPayment 3471 ≤ upperValue ((point split endpoint 4096 3471+point split endpoint 4096 3472)/2)
    have hp : upperPayment 3471 = (97468104209:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3471+point split endpoint 4096 3472)/2 = (663459777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663459777:ℝ)/168755200)*ClassicalSixthBranch.v ((663459777:ℝ)/168755200)/ClassicalSixthBranch.r = (84845082777105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3471
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_216
