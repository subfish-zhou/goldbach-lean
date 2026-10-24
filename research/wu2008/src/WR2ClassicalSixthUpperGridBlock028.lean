import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints028
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_028 (j : Fin 16) : upperPayment (16*28+j.val) ≤
    upperValue ((point split endpoint 4096 (16*28+j.val)+point split endpoint 4096 (16*28+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 448 ≤ upperValue ((point split endpoint 4096 448+point split endpoint 4096 449)/2)
    have hp : upperPayment 448 = (398088214868:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 448+point split endpoint 4096 449)/2 = (587431327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587431327:ℝ)/168755200)*ClassicalSixthBranch.v ((587431327:ℝ)/168755200)/ClassicalSixthBranch.r = (151502643131217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_448
  · change upperPayment 449 ≤ upperValue ((point split endpoint 4096 449+point split endpoint 4096 450)/2)
    have hp : upperPayment 449 = (398025278834:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 449+point split endpoint 4096 450)/2 = (587456477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587456477:ℝ)/168755200)*ClassicalSixthBranch.v ((587456477:ℝ)/168755200)/ClassicalSixthBranch.r = (151477534622681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_449
  · change upperPayment 450 ≤ upperValue ((point split endpoint 4096 450+point split endpoint 4096 451)/2)
    have hp : upperPayment 450 = (397962322487:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 450+point split endpoint 4096 451)/2 = (587481627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587481627:ℝ)/168755200)*ClassicalSixthBranch.v ((587481627:ℝ)/168755200)/ClassicalSixthBranch.r = (151452428138217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_450
  · change upperPayment 451 ≤ upperValue ((point split endpoint 4096 451+point split endpoint 4096 452)/2)
    have hp : upperPayment 451 = (397899345826:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 451+point split endpoint 4096 452)/2 = (587506777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587506777:ℝ)/168755200)*ClassicalSixthBranch.v ((587506777:ℝ)/168755200)/ClassicalSixthBranch.r = (151427323677825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_451
  · change upperPayment 452 ≤ upperValue ((point split endpoint 4096 452+point split endpoint 4096 453)/2)
    have hp : upperPayment 452 = (397836348847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 452+point split endpoint 4096 453)/2 = (587531927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587531927:ℝ)/168755200)*ClassicalSixthBranch.v ((587531927:ℝ)/168755200)/ClassicalSixthBranch.r = (151402221241505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_452
  · change upperPayment 453 ≤ upperValue ((point split endpoint 4096 453+point split endpoint 4096 454)/2)
    have hp : upperPayment 453 = (397773331549:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 453+point split endpoint 4096 454)/2 = (587557077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587557077:ℝ)/168755200)*ClassicalSixthBranch.v ((587557077:ℝ)/168755200)/ClassicalSixthBranch.r = (151377120829257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_453
  · change upperPayment 454 ≤ upperValue ((point split endpoint 4096 454+point split endpoint 4096 455)/2)
    have hp : upperPayment 454 = (397710293928:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 454+point split endpoint 4096 455)/2 = (587582227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587582227:ℝ)/168755200)*ClassicalSixthBranch.v ((587582227:ℝ)/168755200)/ClassicalSixthBranch.r = (151352022441081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_454
  · change upperPayment 455 ≤ upperValue ((point split endpoint 4096 455+point split endpoint 4096 456)/2)
    have hp : upperPayment 455 = (397647235981:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 455+point split endpoint 4096 456)/2 = (587607377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587607377:ℝ)/168755200)*ClassicalSixthBranch.v ((587607377:ℝ)/168755200)/ClassicalSixthBranch.r = (151326926076977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_455
  · change upperPayment 456 ≤ upperValue ((point split endpoint 4096 456+point split endpoint 4096 457)/2)
    have hp : upperPayment 456 = (397584157707:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 456+point split endpoint 4096 457)/2 = (587632527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587632527:ℝ)/168755200)*ClassicalSixthBranch.v ((587632527:ℝ)/168755200)/ClassicalSixthBranch.r = (151301831736945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_456
  · change upperPayment 457 ≤ upperValue ((point split endpoint 4096 457+point split endpoint 4096 458)/2)
    have hp : upperPayment 457 = (397521059102:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 457+point split endpoint 4096 458)/2 = (587657677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587657677:ℝ)/168755200)*ClassicalSixthBranch.v ((587657677:ℝ)/168755200)/ClassicalSixthBranch.r = (151276739420985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_457
  · change upperPayment 458 ≤ upperValue ((point split endpoint 4096 458+point split endpoint 4096 459)/2)
    have hp : upperPayment 458 = (397457940164:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 458+point split endpoint 4096 459)/2 = (587682827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587682827:ℝ)/168755200)*ClassicalSixthBranch.v ((587682827:ℝ)/168755200)/ClassicalSixthBranch.r = (151251649129097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_458
  · change upperPayment 459 ≤ upperValue ((point split endpoint 4096 459+point split endpoint 4096 460)/2)
    have hp : upperPayment 459 = (397394800890:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 459+point split endpoint 4096 460)/2 = (587707977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587707977:ℝ)/168755200)*ClassicalSixthBranch.v ((587707977:ℝ)/168755200)/ClassicalSixthBranch.r = (151226560861281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_459
  · change upperPayment 460 ≤ upperValue ((point split endpoint 4096 460+point split endpoint 4096 461)/2)
    have hp : upperPayment 460 = (397331641277:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 460+point split endpoint 4096 461)/2 = (587733127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587733127:ℝ)/168755200)*ClassicalSixthBranch.v ((587733127:ℝ)/168755200)/ClassicalSixthBranch.r = (151201474617537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_460
  · change upperPayment 461 ≤ upperValue ((point split endpoint 4096 461+point split endpoint 4096 462)/2)
    have hp : upperPayment 461 = (397268461323:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 461+point split endpoint 4096 462)/2 = (587758277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587758277:ℝ)/168755200)*ClassicalSixthBranch.v ((587758277:ℝ)/168755200)/ClassicalSixthBranch.r = (151176390397865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_461
  · change upperPayment 462 ≤ upperValue ((point split endpoint 4096 462+point split endpoint 4096 463)/2)
    have hp : upperPayment 462 = (397205261025:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 462+point split endpoint 4096 463)/2 = (587783427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587783427:ℝ)/168755200)*ClassicalSixthBranch.v ((587783427:ℝ)/168755200)/ClassicalSixthBranch.r = (151151308202265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_462
  · change upperPayment 463 ≤ upperValue ((point split endpoint 4096 463+point split endpoint 4096 464)/2)
    have hp : upperPayment 463 = (397142040381:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 463+point split endpoint 4096 464)/2 = (587808577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587808577:ℝ)/168755200)*ClassicalSixthBranch.v ((587808577:ℝ)/168755200)/ClassicalSixthBranch.r = (151126228030737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_463
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_028
