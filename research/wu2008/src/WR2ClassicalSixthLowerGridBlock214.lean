import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints214
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_214 (j : Fin 16) : lowerPayment (16*214+j.val) ≤
    lowerValue ((point 2 split 4096 (16*214+j.val)+point 2 split 4096 (16*214+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3424 ≤ lowerValue ((point 2 split 4096 3424+point 2 split 4096 3425)/2)
    have hp : lowerPayment 3424 = (359416982908:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3424+point 2 split 4096 3425)/2 = (537028619:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537028619:ℝ)/168755200)/ClassicalSixthBranch.v ((537028619:ℝ)/168755200) = (549254500091:ℝ)/256175447192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3424
  · change lowerPayment 3425 ≤ lowerValue ((point 2 split 4096 3425+point 2 split 4096 3426)/2)
    have hp : lowerPayment 3425 = (359508777220:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3425+point 2 split 4096 3426)/2 = (537086881:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537086881:ℝ)/168755200)/ClassicalSixthBranch.v ((537086881:ℝ)/168755200) = (549177186417:ℝ)/256127439304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3425
  · change lowerPayment 3426 ≤ lowerValue ((point 2 split 4096 3426+point 2 split 4096 3427)/2)
    have hp : lowerPayment 3426 = (359600582383:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3426+point 2 split 4096 3427)/2 = (537145143:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537145143:ℝ)/168755200)/ClassicalSixthBranch.v ((537145143:ℝ)/168755200) = (549099872743:ℝ)/256079431416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3426
  · change lowerPayment 3427 ≤ lowerValue ((point 2 split 4096 3427+point 2 split 4096 3428)/2)
    have hp : lowerPayment 3427 = (359692398412:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3427+point 2 split 4096 3428)/2 = (107440681:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107440681:ℝ)/33751040)/ClassicalSixthBranch.v ((107440681:ℝ)/33751040) = (549022559069:ℝ)/256031423528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3427
  · change lowerPayment 3428 ≤ lowerValue ((point 2 split 4096 3428+point 2 split 4096 3429)/2)
    have hp : lowerPayment 3428 = (359784225322:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3428+point 2 split 4096 3429)/2 = (537261667:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537261667:ℝ)/168755200)/ClassicalSixthBranch.v ((537261667:ℝ)/168755200) = (109789049079:ℝ)/51196683128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3428
  · change lowerPayment 3429 ≤ lowerValue ((point 2 split 4096 3429+point 2 split 4096 3430)/2)
    have hp : lowerPayment 3429 = (359876063128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3429+point 2 split 4096 3430)/2 = (537319929:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537319929:ℝ)/168755200)/ClassicalSixthBranch.v ((537319929:ℝ)/168755200) = (548867931721:ℝ)/255935407752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3429
  · change lowerPayment 3430 ≤ lowerValue ((point 2 split 4096 3430+point 2 split 4096 3431)/2)
    have hp : lowerPayment 3430 = (359967911846:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3430+point 2 split 4096 3431)/2 = (537378191:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537378191:ℝ)/168755200)/ClassicalSixthBranch.v ((537378191:ℝ)/168755200) = (548790618047:ℝ)/255887399864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3430
  · change lowerPayment 3431 ≤ lowerValue ((point 2 split 4096 3431+point 2 split 4096 3432)/2)
    have hp : lowerPayment 3431 = (360059771490:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3431+point 2 split 4096 3432)/2 = (537436453:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537436453:ℝ)/168755200)/ClassicalSixthBranch.v ((537436453:ℝ)/168755200) = (548713304373:ℝ)/255839391976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3431
  · change lowerPayment 3432 ≤ lowerValue ((point 2 split 4096 3432+point 2 split 4096 3433)/2)
    have hp : lowerPayment 3432 = (360151642077:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3432+point 2 split 4096 3433)/2 = (107498943:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107498943:ℝ)/33751040)/ClassicalSixthBranch.v ((107498943:ℝ)/33751040) = (413440837:ℝ)/192759144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3432
  · change lowerPayment 3433 ≤ lowerValue ((point 2 split 4096 3433+point 2 split 4096 3434)/2)
    have hp : lowerPayment 3433 = (360243523620:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3433+point 2 split 4096 3434)/2 = (537552977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537552977:ℝ)/168755200)/ClassicalSixthBranch.v ((537552977:ℝ)/168755200) = (21942347081:ℝ)/10229735048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3433
  · change lowerPayment 3434 ≤ lowerValue ((point 2 split 4096 3434+point 2 split 4096 3435)/2)
    have hp : lowerPayment 3434 = (360335416136:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3434+point 2 split 4096 3435)/2 = (537611239:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537611239:ℝ)/168755200)/ClassicalSixthBranch.v ((537611239:ℝ)/168755200) = (548481363351:ℝ)/255695368312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3434
  · change lowerPayment 3435 ≤ lowerValue ((point 2 split 4096 3435+point 2 split 4096 3436)/2)
    have hp : lowerPayment 3435 = (360427319639:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3435+point 2 split 4096 3436)/2 = (537669501:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537669501:ℝ)/168755200)/ClassicalSixthBranch.v ((537669501:ℝ)/168755200) = (548404049677:ℝ)/255647360424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3435
  · change lowerPayment 3436 ≤ lowerValue ((point 2 split 4096 3436+point 2 split 4096 3437)/2)
    have hp : lowerPayment 3436 = (360519234145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3436+point 2 split 4096 3437)/2 = (537727763:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537727763:ℝ)/168755200)/ClassicalSixthBranch.v ((537727763:ℝ)/168755200) = (548326736003:ℝ)/255599352536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3436
  · change lowerPayment 3437 ≤ lowerValue ((point 2 split 4096 3437+point 2 split 4096 3438)/2)
    have hp : lowerPayment 3437 = (360611159669:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3437+point 2 split 4096 3438)/2 = (21511441:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21511441:ℝ)/6750208)/ClassicalSixthBranch.v ((21511441:ℝ)/6750208) = (548249422329:ℝ)/255551344648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3437
  · change lowerPayment 3438 ≤ lowerValue ((point 2 split 4096 3438+point 2 split 4096 3439)/2)
    have hp : lowerPayment 3438 = (360703096226:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3438+point 2 split 4096 3439)/2 = (537844287:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537844287:ℝ)/168755200)/ClassicalSixthBranch.v ((537844287:ℝ)/168755200) = (217961077:ℝ)/101591784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3438
  · change lowerPayment 3439 ≤ lowerValue ((point 2 split 4096 3439+point 2 split 4096 3440)/2)
    have hp : lowerPayment 3439 = (360795043832:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3439+point 2 split 4096 3440)/2 = (537902549:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537902549:ℝ)/168755200)/ClassicalSixthBranch.v ((537902549:ℝ)/168755200) = (548094794981:ℝ)/255455328872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3439
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_214
