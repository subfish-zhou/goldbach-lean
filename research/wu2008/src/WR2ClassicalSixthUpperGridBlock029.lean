import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints029
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_029 (j : Fin 16) : upperPayment (16*29+j.val) ≤
    upperValue ((point split endpoint 4096 (16*29+j.val)+point split endpoint 4096 (16*29+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 464 ≤ upperValue ((point split endpoint 4096 464+point split endpoint 4096 465)/2)
    have hp : upperPayment 464 = (397078799387:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 464+point split endpoint 4096 465)/2 = (587833727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587833727:ℝ)/168755200)*ClassicalSixthBranch.v ((587833727:ℝ)/168755200)/ClassicalSixthBranch.r = (151101149883281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_464
  · change upperPayment 465 ≤ upperValue ((point split endpoint 4096 465+point split endpoint 4096 466)/2)
    have hp : upperPayment 465 = (397015538041:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 465+point split endpoint 4096 466)/2 = (587858877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587858877:ℝ)/168755200)*ClassicalSixthBranch.v ((587858877:ℝ)/168755200)/ClassicalSixthBranch.r = (151076073759897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_465
  · change upperPayment 466 ≤ upperValue ((point split endpoint 4096 466+point split endpoint 4096 467)/2)
    have hp : upperPayment 466 = (396952256341:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 466+point split endpoint 4096 467)/2 = (587884027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587884027:ℝ)/168755200)*ClassicalSixthBranch.v ((587884027:ℝ)/168755200)/ClassicalSixthBranch.r = (151050999660585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_466
  · change upperPayment 467 ≤ upperValue ((point split endpoint 4096 467+point split endpoint 4096 468)/2)
    have hp : upperPayment 467 = (396888954283:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 467+point split endpoint 4096 468)/2 = (587909177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587909177:ℝ)/168755200)*ClassicalSixthBranch.v ((587909177:ℝ)/168755200)/ClassicalSixthBranch.r = (151025927585345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_467
  · change upperPayment 468 ≤ upperValue ((point split endpoint 4096 468+point split endpoint 4096 469)/2)
    have hp : upperPayment 468 = (396825631866:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 468+point split endpoint 4096 469)/2 = (587934327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587934327:ℝ)/168755200)*ClassicalSixthBranch.v ((587934327:ℝ)/168755200)/ClassicalSixthBranch.r = (151000857534177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_468
  · change upperPayment 469 ≤ upperValue ((point split endpoint 4096 469+point split endpoint 4096 470)/2)
    have hp : upperPayment 469 = (396762289086:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 469+point split endpoint 4096 470)/2 = (587959477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587959477:ℝ)/168755200)*ClassicalSixthBranch.v ((587959477:ℝ)/168755200)/ClassicalSixthBranch.r = (150975789507081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_469
  · change upperPayment 470 ≤ upperValue ((point split endpoint 4096 470+point split endpoint 4096 471)/2)
    have hp : upperPayment 470 = (396698925941:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 470+point split endpoint 4096 471)/2 = (587984627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587984627:ℝ)/168755200)*ClassicalSixthBranch.v ((587984627:ℝ)/168755200)/ClassicalSixthBranch.r = (150950723504057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_470
  · change upperPayment 471 ≤ upperValue ((point split endpoint 4096 471+point split endpoint 4096 472)/2)
    have hp : upperPayment 471 = (396635542427:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 471+point split endpoint 4096 472)/2 = (588009777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588009777:ℝ)/168755200)*ClassicalSixthBranch.v ((588009777:ℝ)/168755200)/ClassicalSixthBranch.r = (150925659525105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_471
  · change upperPayment 472 ≤ upperValue ((point split endpoint 4096 472+point split endpoint 4096 473)/2)
    have hp : upperPayment 472 = (396572138543:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 472+point split endpoint 4096 473)/2 = (588034927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588034927:ℝ)/168755200)*ClassicalSixthBranch.v ((588034927:ℝ)/168755200)/ClassicalSixthBranch.r = (150900597570225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_472
  · change upperPayment 473 ≤ upperValue ((point split endpoint 4096 473+point split endpoint 4096 474)/2)
    have hp : upperPayment 473 = (396508714286:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 473+point split endpoint 4096 474)/2 = (588060077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588060077:ℝ)/168755200)*ClassicalSixthBranch.v ((588060077:ℝ)/168755200)/ClassicalSixthBranch.r = (150875537639417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_473
  · change upperPayment 474 ≤ upperValue ((point split endpoint 4096 474+point split endpoint 4096 475)/2)
    have hp : upperPayment 474 = (396445269653:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 474+point split endpoint 4096 475)/2 = (588085227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588085227:ℝ)/168755200)*ClassicalSixthBranch.v ((588085227:ℝ)/168755200)/ClassicalSixthBranch.r = (150850479732681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_474
  · change upperPayment 475 ≤ upperValue ((point split endpoint 4096 475+point split endpoint 4096 476)/2)
    have hp : upperPayment 475 = (396381804641:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 475+point split endpoint 4096 476)/2 = (588110377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588110377:ℝ)/168755200)*ClassicalSixthBranch.v ((588110377:ℝ)/168755200)/ClassicalSixthBranch.r = (150825423850017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_475
  · change upperPayment 476 ≤ upperValue ((point split endpoint 4096 476+point split endpoint 4096 477)/2)
    have hp : upperPayment 476 = (396318319248:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 476+point split endpoint 4096 477)/2 = (588135527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588135527:ℝ)/168755200)*ClassicalSixthBranch.v ((588135527:ℝ)/168755200)/ClassicalSixthBranch.r = (150800369991425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_476
  · change upperPayment 477 ≤ upperValue ((point split endpoint 4096 477+point split endpoint 4096 478)/2)
    have hp : upperPayment 477 = (396254813470:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 477+point split endpoint 4096 478)/2 = (588160677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588160677:ℝ)/168755200)*ClassicalSixthBranch.v ((588160677:ℝ)/168755200)/ClassicalSixthBranch.r = (150775318156905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_477
  · change upperPayment 478 ≤ upperValue ((point split endpoint 4096 478+point split endpoint 4096 479)/2)
    have hp : upperPayment 478 = (396191287306:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 478+point split endpoint 4096 479)/2 = (588185827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588185827:ℝ)/168755200)*ClassicalSixthBranch.v ((588185827:ℝ)/168755200)/ClassicalSixthBranch.r = (150750268346457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_478
  · change upperPayment 479 ≤ upperValue ((point split endpoint 4096 479+point split endpoint 4096 480)/2)
    have hp : upperPayment 479 = (396127740753:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 479+point split endpoint 4096 480)/2 = (588210977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588210977:ℝ)/168755200)*ClassicalSixthBranch.v ((588210977:ℝ)/168755200)/ClassicalSixthBranch.r = (150725220560081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_479
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_029
