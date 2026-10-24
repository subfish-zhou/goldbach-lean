import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints023
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_023 (j : Fin 16) : lowerPayment (16*23+j.val) ≤
    lowerValue ((point 2 split 4096 (16*23+j.val)+point 2 split 4096 (16*23+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 368 ≤ lowerValue ((point 2 split 4096 368+point 2 split 4096 369)/2)
    have hp : lowerPayment 368 = (55327983030:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 368+point 2 split 4096 369)/2 = (358979947:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358979947:ℝ)/168755200)/ClassicalSixthBranch.v ((358979947:ℝ)/168755200) = (157105017567:ℝ)/80577510584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_368
  · change lowerPayment 369 ≤ lowerValue ((point 2 split 4096 369+point 2 split 4096 370)/2)
    have hp : lowerPayment 369 = (55466432719:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 369+point 2 split 4096 370)/2 = (359038209:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359038209:ℝ)/168755200)/ClassicalSixthBranch.v ((359038209:ℝ)/168755200) = (785447774161:ℝ)/402839545032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_369
  · change lowerPayment 370 ≤ lowerValue ((point 2 split 4096 370+point 2 split 4096 371)/2)
    have hp : lowerPayment 370 = (55604825921:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 370+point 2 split 4096 371)/2 = (359096471:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359096471:ℝ)/168755200)/ClassicalSixthBranch.v ((359096471:ℝ)/168755200) = (785370460487:ℝ)/402791537144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_370
  · change lowerPayment 371 ≤ lowerValue ((point 2 split 4096 371+point 2 split 4096 372)/2)
    have hp : lowerPayment 371 = (55743162684:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 371+point 2 split 4096 372)/2 = (359154733:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359154733:ℝ)/168755200)/ClassicalSixthBranch.v ((359154733:ℝ)/168755200) = (785293146813:ℝ)/402743529256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_371
  · change lowerPayment 372 ≤ lowerValue ((point 2 split 4096 372+point 2 split 4096 373)/2)
    have hp : lowerPayment 372 = (55881443060:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 372+point 2 split 4096 373)/2 = (71842599:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71842599:ℝ)/33751040)/ClassicalSixthBranch.v ((71842599:ℝ)/33751040) = (785215833139:ℝ)/402695521368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_372
  · change lowerPayment 373 ≤ lowerValue ((point 2 split 4096 373+point 2 split 4096 374)/2)
    have hp : lowerPayment 373 = (56019667099:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 373+point 2 split 4096 374)/2 = (359271257:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359271257:ℝ)/168755200)/ClassicalSixthBranch.v ((359271257:ℝ)/168755200) = (157027703893:ℝ)/80529502696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_373
  · change lowerPayment 374 ≤ lowerValue ((point 2 split 4096 374+point 2 split 4096 375)/2)
    have hp : lowerPayment 374 = (56157834851:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 374+point 2 split 4096 375)/2 = (359329519:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359329519:ℝ)/168755200)/ClassicalSixthBranch.v ((359329519:ℝ)/168755200) = (785061205791:ℝ)/402599505592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_374
  · change lowerPayment 375 ≤ lowerValue ((point 2 split 4096 375+point 2 split 4096 376)/2)
    have hp : lowerPayment 375 = (56295946366:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 375+point 2 split 4096 376)/2 = (359387781:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359387781:ℝ)/168755200)/ClassicalSixthBranch.v ((359387781:ℝ)/168755200) = (784983892117:ℝ)/402551497704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_375
  · change lowerPayment 376 ≤ lowerValue ((point 2 split 4096 376+point 2 split 4096 377)/2)
    have hp : lowerPayment 376 = (56434001693:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 376+point 2 split 4096 377)/2 = (359446043:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359446043:ℝ)/168755200)/ClassicalSixthBranch.v ((359446043:ℝ)/168755200) = (784906578443:ℝ)/402503489816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_376
  · change lowerPayment 377 ≤ lowerValue ((point 2 split 4096 377+point 2 split 4096 378)/2)
    have hp : lowerPayment 377 = (56572000884:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 377+point 2 split 4096 378)/2 = (71900861:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71900861:ℝ)/33751040)/ClassicalSixthBranch.v ((71900861:ℝ)/33751040) = (784829264769:ℝ)/402455481928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_377
  · change lowerPayment 378 ≤ lowerValue ((point 2 split 4096 378+point 2 split 4096 379)/2)
    have hp : lowerPayment 378 = (56709943988:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 378+point 2 split 4096 379)/2 = (359562567:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359562567:ℝ)/168755200)/ClassicalSixthBranch.v ((359562567:ℝ)/168755200) = (156950390219:ℝ)/80481494808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_378
  · change lowerPayment 379 ≤ lowerValue ((point 2 split 4096 379+point 2 split 4096 380)/2)
    have hp : lowerPayment 379 = (56847831055:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 379+point 2 split 4096 380)/2 = (359620829:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359620829:ℝ)/168755200)/ClassicalSixthBranch.v ((359620829:ℝ)/168755200) = (784674637421:ℝ)/402359466152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_379
  · change lowerPayment 380 ≤ lowerValue ((point 2 split 4096 380+point 2 split 4096 381)/2)
    have hp : lowerPayment 380 = (56985662134:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 380+point 2 split 4096 381)/2 = (359679091:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359679091:ℝ)/168755200)/ClassicalSixthBranch.v ((359679091:ℝ)/168755200) = (784597323747:ℝ)/402311458264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_380
  · change lowerPayment 381 ≤ lowerValue ((point 2 split 4096 381+point 2 split 4096 382)/2)
    have hp : lowerPayment 381 = (57123437276:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 381+point 2 split 4096 382)/2 = (359737353:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359737353:ℝ)/168755200)/ClassicalSixthBranch.v ((359737353:ℝ)/168755200) = (784520010073:ℝ)/402263450376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_381
  · change lowerPayment 382 ≤ lowerValue ((point 2 split 4096 382+point 2 split 4096 383)/2)
    have hp : lowerPayment 382 = (57261156531:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 382+point 2 split 4096 383)/2 = (71959123:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71959123:ℝ)/33751040)/ClassicalSixthBranch.v ((71959123:ℝ)/33751040) = (784442696399:ℝ)/402215442488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_382
  · change lowerPayment 383 ≤ lowerValue ((point 2 split 4096 383+point 2 split 4096 384)/2)
    have hp : lowerPayment 383 = (57398819947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 383+point 2 split 4096 384)/2 = (359853877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359853877:ℝ)/168755200)/ClassicalSixthBranch.v ((359853877:ℝ)/168755200) = (31374615309:ℝ)/16086697384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_383
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_023
