import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints029
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_029 (j : Fin 16) : lowerPayment (16*29+j.val) ≤
    lowerValue ((point 2 split 4096 (16*29+j.val)+point 2 split 4096 (16*29+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 464 ≤ lowerValue ((point 2 split 4096 464+point 2 split 4096 465)/2)
    have hp : lowerPayment 464 = (68368600996:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 464+point 2 split 4096 465)/2 = (364573099:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364573099:ℝ)/168755200)/ClassicalSixthBranch.v ((364573099:ℝ)/168755200) = (778102975131:ℝ)/398278795672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_464
  · change lowerPayment 465 ≤ lowerValue ((point 2 split 4096 465+point 2 split 4096 466)/2)
    have hp : lowerPayment 465 = (68501850642:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 465+point 2 split 4096 466)/2 = (364631361:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364631361:ℝ)/168755200)/ClassicalSixthBranch.v ((364631361:ℝ)/168755200) = (778025661457:ℝ)/398230787784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_465
  · change lowerPayment 466 ≤ lowerValue ((point 2 split 4096 466+point 2 split 4096 467)/2)
    have hp : lowerPayment 466 = (68635048422:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 466+point 2 split 4096 467)/2 = (364689623:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364689623:ℝ)/168755200)/ClassicalSixthBranch.v ((364689623:ℝ)/168755200) = (777948347783:ℝ)/398182779896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_466
  · change lowerPayment 467 ≤ lowerValue ((point 2 split 4096 467+point 2 split 4096 468)/2)
    have hp : lowerPayment 467 = (68768194381:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 467+point 2 split 4096 468)/2 = (72949577:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72949577:ℝ)/33751040)/ClassicalSixthBranch.v ((72949577:ℝ)/33751040) = (777871034109:ℝ)/398134772008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_467
  · change lowerPayment 468 ≤ lowerValue ((point 2 split 4096 468+point 2 split 4096 469)/2)
    have hp : lowerPayment 468 = (68901288566:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 468+point 2 split 4096 469)/2 = (364806147:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364806147:ℝ)/168755200)/ClassicalSixthBranch.v ((364806147:ℝ)/168755200) = (155558744087:ℝ)/79617352824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_468
  · change lowerPayment 469 ≤ lowerValue ((point 2 split 4096 469+point 2 split 4096 470)/2)
    have hp : lowerPayment 469 = (69034331023:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 469+point 2 split 4096 470)/2 = (364864409:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364864409:ℝ)/168755200)/ClassicalSixthBranch.v ((364864409:ℝ)/168755200) = (777716406761:ℝ)/398038756232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_469
  · change lowerPayment 470 ≤ lowerValue ((point 2 split 4096 470+point 2 split 4096 471)/2)
    have hp : lowerPayment 470 = (69167321798:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 470+point 2 split 4096 471)/2 = (364922671:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364922671:ℝ)/168755200)/ClassicalSixthBranch.v ((364922671:ℝ)/168755200) = (777639093087:ℝ)/397990748344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_470
  · change lowerPayment 471 ≤ lowerValue ((point 2 split 4096 471+point 2 split 4096 472)/2)
    have hp : lowerPayment 471 = (69300260936:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 471+point 2 split 4096 472)/2 = (364980933:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((364980933:ℝ)/168755200)/ClassicalSixthBranch.v ((364980933:ℝ)/168755200) = (777561779413:ℝ)/397942740456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_471
  · change lowerPayment 472 ≤ lowerValue ((point 2 split 4096 472+point 2 split 4096 473)/2)
    have hp : lowerPayment 472 = (69433148483:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 472+point 2 split 4096 473)/2 = (73007839:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73007839:ℝ)/33751040)/ClassicalSixthBranch.v ((73007839:ℝ)/33751040) = (777484465739:ℝ)/397894732568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_472
  · change lowerPayment 473 ≤ lowerValue ((point 2 split 4096 473+point 2 split 4096 474)/2)
    have hp : lowerPayment 473 = (69565984486:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 473+point 2 split 4096 474)/2 = (365097457:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365097457:ℝ)/168755200)/ClassicalSixthBranch.v ((365097457:ℝ)/168755200) = (155481430413:ℝ)/79569344936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_473
  · change lowerPayment 474 ≤ lowerValue ((point 2 split 4096 474+point 2 split 4096 475)/2)
    have hp : lowerPayment 474 = (69698768989:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 474+point 2 split 4096 475)/2 = (365155719:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365155719:ℝ)/168755200)/ClassicalSixthBranch.v ((365155719:ℝ)/168755200) = (777329838391:ℝ)/397798716792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_474
  · change lowerPayment 475 ≤ lowerValue ((point 2 split 4096 475+point 2 split 4096 476)/2)
    have hp : lowerPayment 475 = (69831502039:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 475+point 2 split 4096 476)/2 = (365213981:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365213981:ℝ)/168755200)/ClassicalSixthBranch.v ((365213981:ℝ)/168755200) = (777252524717:ℝ)/397750708904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_475
  · change lowerPayment 476 ≤ lowerValue ((point 2 split 4096 476+point 2 split 4096 477)/2)
    have hp : lowerPayment 476 = (69964183681:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 476+point 2 split 4096 477)/2 = (365272243:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365272243:ℝ)/168755200)/ClassicalSixthBranch.v ((365272243:ℝ)/168755200) = (777175211043:ℝ)/397702701016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_476
  · change lowerPayment 477 ≤ lowerValue ((point 2 split 4096 477+point 2 split 4096 478)/2)
    have hp : lowerPayment 477 = (70096813960:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 477+point 2 split 4096 478)/2 = (73066101:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73066101:ℝ)/33751040)/ClassicalSixthBranch.v ((73066101:ℝ)/33751040) = (777097897369:ℝ)/397654693128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_477
  · change lowerPayment 478 ≤ lowerValue ((point 2 split 4096 478+point 2 split 4096 479)/2)
    have hp : lowerPayment 478 = (70229392924:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 478+point 2 split 4096 479)/2 = (365388767:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365388767:ℝ)/168755200)/ClassicalSixthBranch.v ((365388767:ℝ)/168755200) = (155404116739:ℝ)/79521337048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_478
  · change lowerPayment 479 ≤ lowerValue ((point 2 split 4096 479+point 2 split 4096 480)/2)
    have hp : lowerPayment 479 = (70361920616:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 479+point 2 split 4096 480)/2 = (365447029:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365447029:ℝ)/168755200)/ClassicalSixthBranch.v ((365447029:ℝ)/168755200) = (776943270021:ℝ)/397558677352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_479
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_029
