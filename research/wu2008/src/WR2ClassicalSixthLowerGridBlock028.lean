import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints028
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_028 (j : Fin 16) : lowerPayment (16*28+j.val) ≤
    lowerValue ((point 2 split 4096 (16*28+j.val)+point 2 split 4096 (16*28+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 448 ≤ lowerValue ((point 2 split 4096 448+point 2 split 4096 449)/2)
    have hp : lowerPayment 448 = (66229515125:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 448+point 2 split 4096 449)/2 = (363640907:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363640907:ℝ)/168755200)/ClassicalSixthBranch.v ((363640907:ℝ)/168755200) = (155867998783:ℝ)/79809384376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_448
  · change lowerPayment 449 ≤ lowerValue ((point 2 split 4096 449+point 2 split 4096 450)/2)
    have hp : lowerPayment 449 = (66363600926:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 449+point 2 split 4096 450)/2 = (363699169:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363699169:ℝ)/168755200)/ClassicalSixthBranch.v ((363699169:ℝ)/168755200) = (779262680241:ℝ)/398998913992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_449
  · change lowerPayment 450 ≤ lowerValue ((point 2 split 4096 450+point 2 split 4096 451)/2)
    have hp : lowerPayment 450 = (66497634119:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 450+point 2 split 4096 451)/2 = (363757431:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363757431:ℝ)/168755200)/ClassicalSixthBranch.v ((363757431:ℝ)/168755200) = (779185366567:ℝ)/398950906104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_450
  · change lowerPayment 451 ≤ lowerValue ((point 2 split 4096 451+point 2 split 4096 452)/2)
    have hp : lowerPayment 451 = (66631614749:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 451+point 2 split 4096 452)/2 = (363815693:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363815693:ℝ)/168755200)/ClassicalSixthBranch.v ((363815693:ℝ)/168755200) = (779108052893:ℝ)/398902898216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_451
  · change lowerPayment 452 ≤ lowerValue ((point 2 split 4096 452+point 2 split 4096 453)/2)
    have hp : lowerPayment 452 = (66765542864:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 452+point 2 split 4096 453)/2 = (72774791:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72774791:ℝ)/33751040)/ClassicalSixthBranch.v ((72774791:ℝ)/33751040) = (779030739219:ℝ)/398854890328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_452
  · change lowerPayment 453 ≤ lowerValue ((point 2 split 4096 453+point 2 split 4096 454)/2)
    have hp : lowerPayment 453 = (66899418511:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 453+point 2 split 4096 454)/2 = (363932217:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363932217:ℝ)/168755200)/ClassicalSixthBranch.v ((363932217:ℝ)/168755200) = (155790685109:ℝ)/79761376488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_453
  · change lowerPayment 454 ≤ lowerValue ((point 2 split 4096 454+point 2 split 4096 455)/2)
    have hp : lowerPayment 454 = (67033241736:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 454+point 2 split 4096 455)/2 = (363990479:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((363990479:ℝ)/168755200)/ClassicalSixthBranch.v ((363990479:ℝ)/168755200) = (778876111871:ℝ)/398758874552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_454
  · change lowerPayment 455 ≤ lowerValue ((point 2 split 4096 455+point 2 split 4096 456)/2)
    have hp : lowerPayment 455 = (67167012586:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 455+point 2 split 4096 456)/2 = (364048741:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364048741:ℝ)/168755200)/ClassicalSixthBranch.v ((364048741:ℝ)/168755200) = (778798798197:ℝ)/398710866664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_455
  · change lowerPayment 456 ≤ lowerValue ((point 2 split 4096 456+point 2 split 4096 457)/2)
    have hp : lowerPayment 456 = (67300731106:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 456+point 2 split 4096 457)/2 = (364107003:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364107003:ℝ)/168755200)/ClassicalSixthBranch.v ((364107003:ℝ)/168755200) = (778721484523:ℝ)/398662858776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_456
  · change lowerPayment 457 ≤ lowerValue ((point 2 split 4096 457+point 2 split 4096 458)/2)
    have hp : lowerPayment 457 = (67434397344:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 457+point 2 split 4096 458)/2 = (72833053:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72833053:ℝ)/33751040)/ClassicalSixthBranch.v ((72833053:ℝ)/33751040) = (778644170849:ℝ)/398614850888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_457
  · change lowerPayment 458 ≤ lowerValue ((point 2 split 4096 458+point 2 split 4096 459)/2)
    have hp : lowerPayment 458 = (67568011347:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 458+point 2 split 4096 459)/2 = (364223527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364223527:ℝ)/168755200)/ClassicalSixthBranch.v ((364223527:ℝ)/168755200) = (31142674287:ℝ)/15942673720 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_458
  · change lowerPayment 459 ≤ lowerValue ((point 2 split 4096 459+point 2 split 4096 460)/2)
    have hp : lowerPayment 459 = (67701573159:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 459+point 2 split 4096 460)/2 = (364281789:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364281789:ℝ)/168755200)/ClassicalSixthBranch.v ((364281789:ℝ)/168755200) = (778489543501:ℝ)/398518835112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_459
  · change lowerPayment 460 ≤ lowerValue ((point 2 split 4096 460+point 2 split 4096 461)/2)
    have hp : lowerPayment 460 = (67835082828:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 460+point 2 split 4096 461)/2 = (364340051:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364340051:ℝ)/168755200)/ClassicalSixthBranch.v ((364340051:ℝ)/168755200) = (778412229827:ℝ)/398470827224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_460
  · change lowerPayment 461 ≤ lowerValue ((point 2 split 4096 461+point 2 split 4096 462)/2)
    have hp : lowerPayment 461 = (67968540400:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 461+point 2 split 4096 462)/2 = (364398313:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364398313:ℝ)/168755200)/ClassicalSixthBranch.v ((364398313:ℝ)/168755200) = (778334916153:ℝ)/398422819336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_461
  · change lowerPayment 462 ≤ lowerValue ((point 2 split 4096 462+point 2 split 4096 463)/2)
    have hp : lowerPayment 462 = (68101945921:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 462+point 2 split 4096 463)/2 = (14578263:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14578263:ℝ)/6750208)/ClassicalSixthBranch.v ((14578263:ℝ)/6750208) = (778257602479:ℝ)/398374811448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_462
  · change lowerPayment 463 ≤ lowerValue ((point 2 split 4096 463+point 2 split 4096 464)/2)
    have hp : lowerPayment 463 = (68235299438:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 463+point 2 split 4096 464)/2 = (3538979:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3538979:ℝ)/1638400)/ClassicalSixthBranch.v ((3538979:ℝ)/1638400) = (1511029687:ℝ)/773450104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_463
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_028
