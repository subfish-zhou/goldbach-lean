import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints024
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_024 (j : Fin 16) : upperPayment (16*24+j.val) ≤
    upperValue ((point split endpoint 4096 (16*24+j.val)+point split endpoint 4096 (16*24+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 384 ≤ upperValue ((point split endpoint 4096 384+point split endpoint 4096 385)/2)
    have hp : upperPayment 384 = (402073992371:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 384+point split endpoint 4096 385)/2 = (585821727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585821727:ℝ)/168755200)*ClassicalSixthBranch.v ((585821727:ℝ)/168755200)/ClassicalSixthBranch.r = (153113797747281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_384
  · change upperPayment 385 ≤ upperValue ((point split endpoint 4096 385+point split endpoint 4096 386)/2)
    have hp : upperPayment 385 = (402012350851:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 385+point split endpoint 4096 386)/2 = (585846877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585846877:ℝ)/168755200)*ClassicalSixthBranch.v ((585846877:ℝ)/168755200)/ClassicalSixthBranch.r = (153088559698137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_385
  · change upperPayment 386 ≤ upperValue ((point split endpoint 4096 386+point split endpoint 4096 387)/2)
    have hp : upperPayment 386 = (401950689186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 386+point split endpoint 4096 387)/2 = (585872027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585872027:ℝ)/168755200)*ClassicalSixthBranch.v ((585872027:ℝ)/168755200)/ClassicalSixthBranch.r = (153063323673065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_386
  · change upperPayment 387 ≤ upperValue ((point split endpoint 4096 387+point split endpoint 4096 388)/2)
    have hp : upperPayment 387 = (401889007374:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 387+point split endpoint 4096 388)/2 = (585897177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585897177:ℝ)/168755200)*ClassicalSixthBranch.v ((585897177:ℝ)/168755200)/ClassicalSixthBranch.r = (153038089672065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_387
  · change upperPayment 388 ≤ upperValue ((point split endpoint 4096 388+point split endpoint 4096 389)/2)
    have hp : upperPayment 388 = (401827305412:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 388+point split endpoint 4096 389)/2 = (585922327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585922327:ℝ)/168755200)*ClassicalSixthBranch.v ((585922327:ℝ)/168755200)/ClassicalSixthBranch.r = (153012857695137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_388
  · change upperPayment 389 ≤ upperValue ((point split endpoint 4096 389+point split endpoint 4096 390)/2)
    have hp : upperPayment 389 = (401765583297:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 389+point split endpoint 4096 390)/2 = (585947477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585947477:ℝ)/168755200)*ClassicalSixthBranch.v ((585947477:ℝ)/168755200)/ClassicalSixthBranch.r = (152987627742281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_389
  · change upperPayment 390 ≤ upperValue ((point split endpoint 4096 390+point split endpoint 4096 391)/2)
    have hp : upperPayment 390 = (401703841026:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 390+point split endpoint 4096 391)/2 = (585972627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585972627:ℝ)/168755200)*ClassicalSixthBranch.v ((585972627:ℝ)/168755200)/ClassicalSixthBranch.r = (152962399813497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_390
  · change upperPayment 391 ≤ upperValue ((point split endpoint 4096 391+point split endpoint 4096 392)/2)
    have hp : upperPayment 391 = (401642078598:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 391+point split endpoint 4096 392)/2 = (585997777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585997777:ℝ)/168755200)*ClassicalSixthBranch.v ((585997777:ℝ)/168755200)/ClassicalSixthBranch.r = (152937173908785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_391
  · change upperPayment 392 ≤ upperValue ((point split endpoint 4096 392+point split endpoint 4096 393)/2)
    have hp : upperPayment 392 = (401580296009:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 392+point split endpoint 4096 393)/2 = (586022927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586022927:ℝ)/168755200)*ClassicalSixthBranch.v ((586022927:ℝ)/168755200)/ClassicalSixthBranch.r = (152911950028145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_392
  · change upperPayment 393 ≤ upperValue ((point split endpoint 4096 393+point split endpoint 4096 394)/2)
    have hp : upperPayment 393 = (401518493257:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 393+point split endpoint 4096 394)/2 = (586048077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586048077:ℝ)/168755200)*ClassicalSixthBranch.v ((586048077:ℝ)/168755200)/ClassicalSixthBranch.r = (152886728171577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_393
  · change upperPayment 394 ≤ upperValue ((point split endpoint 4096 394+point split endpoint 4096 395)/2)
    have hp : upperPayment 394 = (401456670339:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 394+point split endpoint 4096 395)/2 = (586073227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586073227:ℝ)/168755200)*ClassicalSixthBranch.v ((586073227:ℝ)/168755200)/ClassicalSixthBranch.r = (152861508339081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_394
  · change upperPayment 395 ≤ upperValue ((point split endpoint 4096 395+point split endpoint 4096 396)/2)
    have hp : upperPayment 395 = (401394827254:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 395+point split endpoint 4096 396)/2 = (586098377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586098377:ℝ)/168755200)*ClassicalSixthBranch.v ((586098377:ℝ)/168755200)/ClassicalSixthBranch.r = (152836290530657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_395
  · change upperPayment 396 ≤ upperValue ((point split endpoint 4096 396+point split endpoint 4096 397)/2)
    have hp : upperPayment 396 = (401332963997:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 396+point split endpoint 4096 397)/2 = (586123527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586123527:ℝ)/168755200)*ClassicalSixthBranch.v ((586123527:ℝ)/168755200)/ClassicalSixthBranch.r = (152811074746305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_396
  · change upperPayment 397 ≤ upperValue ((point split endpoint 4096 397+point split endpoint 4096 398)/2)
    have hp : upperPayment 397 = (401271080567:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 397+point split endpoint 4096 398)/2 = (586148677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586148677:ℝ)/168755200)*ClassicalSixthBranch.v ((586148677:ℝ)/168755200)/ClassicalSixthBranch.r = (152785860986025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_397
  · change upperPayment 398 ≤ upperValue ((point split endpoint 4096 398+point split endpoint 4096 399)/2)
    have hp : upperPayment 398 = (401209176961:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 398+point split endpoint 4096 399)/2 = (586173827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586173827:ℝ)/168755200)*ClassicalSixthBranch.v ((586173827:ℝ)/168755200)/ClassicalSixthBranch.r = (152760649249817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_398
  · change upperPayment 399 ≤ upperValue ((point split endpoint 4096 399+point split endpoint 4096 400)/2)
    have hp : upperPayment 399 = (401147253177:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 399+point split endpoint 4096 400)/2 = (586198977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586198977:ℝ)/168755200)*ClassicalSixthBranch.v ((586198977:ℝ)/168755200)/ClassicalSixthBranch.r = (152735439537681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_399
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_024
