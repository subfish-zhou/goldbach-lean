import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints028
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_028 (j : Fin 16) : middlePayment (16*28+j.val) ≤
    middleValue ((point 4 cut 1024 (16*28+j.val)+point 4 cut 1024 (16*28+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 448 ≤ middleValue ((point 4 cut 1024 448+point 4 cut 1024 449)/2)
    have hp : middlePayment 448 = (643112101948:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 448+point 4 cut 1024 449)/2 = (84604541:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84604541:ℝ)/21094400) = (33971200:ℝ)/21385603 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84604541:ℝ)/21094400)-4 = (226941:ℝ)/21094400 by norm_num]
    exact paid_middle_448
  · change middlePayment 449 ≤ middleValue ((point 4 cut 1024 449+point 4 cut 1024 450)/2)
    have hp : middlePayment 449 = (643151663426:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 449+point 4 cut 1024 450)/2 = (84605047:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84605047:ℝ)/21094400) = (33971200:ℝ)/21385097 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84605047:ℝ)/21094400)-4 = (227447:ℝ)/21094400 by norm_num]
    exact paid_middle_449
  · change middlePayment 450 ≤ middleValue ((point 4 cut 1024 450+point 4 cut 1024 451)/2)
    have hp : middlePayment 450 = (643191226442:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 450+point 4 cut 1024 451)/2 = (84605553:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84605553:ℝ)/21094400) = (33971200:ℝ)/21384591 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84605553:ℝ)/21094400)-4 = (227953:ℝ)/21094400 by norm_num]
    exact paid_middle_450
  · change middlePayment 451 ≤ middleValue ((point 4 cut 1024 451+point 4 cut 1024 452)/2)
    have hp : middlePayment 451 = (643230790995:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 451+point 4 cut 1024 452)/2 = (84606059:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84606059:ℝ)/21094400) = (6794240:ℝ)/4276817 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84606059:ℝ)/21094400)-4 = (228459:ℝ)/21094400 by norm_num]
    exact paid_middle_451
  · change middlePayment 452 ≤ middleValue ((point 4 cut 1024 452+point 4 cut 1024 453)/2)
    have hp : middlePayment 452 = (643270357085:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 452+point 4 cut 1024 453)/2 = (16921313:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16921313:ℝ)/4218880) = (33971200:ℝ)/21383579 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16921313:ℝ)/4218880)-4 = (45793:ℝ)/4218880 by norm_num]
    exact paid_middle_452
  · change middlePayment 453 ≤ middleValue ((point 4 cut 1024 453+point 4 cut 1024 454)/2)
    have hp : middlePayment 453 = (643309924713:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 453+point 4 cut 1024 454)/2 = (84607071:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84607071:ℝ)/21094400) = (33971200:ℝ)/21383073 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84607071:ℝ)/21094400)-4 = (229471:ℝ)/21094400 by norm_num]
    exact paid_middle_453
  · change middlePayment 454 ≤ middleValue ((point 4 cut 1024 454+point 4 cut 1024 455)/2)
    have hp : middlePayment 454 = (643349493879:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 454+point 4 cut 1024 455)/2 = (84607577:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84607577:ℝ)/21094400) = (33971200:ℝ)/21382567 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84607577:ℝ)/21094400)-4 = (229977:ℝ)/21094400 by norm_num]
    exact paid_middle_454
  · change middlePayment 455 ≤ middleValue ((point 4 cut 1024 455+point 4 cut 1024 456)/2)
    have hp : middlePayment 455 = (643389064582:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 455+point 4 cut 1024 456)/2 = (84608083:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84608083:ℝ)/21094400) = (33971200:ℝ)/21382061 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84608083:ℝ)/21094400)-4 = (230483:ℝ)/21094400 by norm_num]
    exact paid_middle_455
  · change middlePayment 456 ≤ middleValue ((point 4 cut 1024 456+point 4 cut 1024 457)/2)
    have hp : middlePayment 456 = (643428636823:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 456+point 4 cut 1024 457)/2 = (84608589:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84608589:ℝ)/21094400) = (6794240:ℝ)/4276311 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84608589:ℝ)/21094400)-4 = (230989:ℝ)/21094400 by norm_num]
    exact paid_middle_456
  · change middlePayment 457 ≤ middleValue ((point 4 cut 1024 457+point 4 cut 1024 458)/2)
    have hp : middlePayment 457 = (643468210602:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 457+point 4 cut 1024 458)/2 = (16921819:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16921819:ℝ)/4218880) = (33971200:ℝ)/21381049 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16921819:ℝ)/4218880)-4 = (46299:ℝ)/4218880 by norm_num]
    exact paid_middle_457
  · change middlePayment 458 ≤ middleValue ((point 4 cut 1024 458+point 4 cut 1024 459)/2)
    have hp : middlePayment 458 = (643507785919:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 458+point 4 cut 1024 459)/2 = (84609601:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84609601:ℝ)/21094400) = (33971200:ℝ)/21380543 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84609601:ℝ)/21094400)-4 = (232001:ℝ)/21094400 by norm_num]
    exact paid_middle_458
  · change middlePayment 459 ≤ middleValue ((point 4 cut 1024 459+point 4 cut 1024 460)/2)
    have hp : middlePayment 459 = (643547362773:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 459+point 4 cut 1024 460)/2 = (84610107:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84610107:ℝ)/21094400) = (33971200:ℝ)/21380037 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84610107:ℝ)/21094400)-4 = (232507:ℝ)/21094400 by norm_num]
    exact paid_middle_459
  · change middlePayment 460 ≤ middleValue ((point 4 cut 1024 460+point 4 cut 1024 461)/2)
    have hp : middlePayment 460 = (643586941166:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 460+point 4 cut 1024 461)/2 = (84610613:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84610613:ℝ)/21094400) = (33971200:ℝ)/21379531 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84610613:ℝ)/21094400)-4 = (233013:ℝ)/21094400 by norm_num]
    exact paid_middle_460
  · change middlePayment 461 ≤ middleValue ((point 4 cut 1024 461+point 4 cut 1024 462)/2)
    have hp : middlePayment 461 = (643626521097:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 461+point 4 cut 1024 462)/2 = (84611119:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84611119:ℝ)/21094400) = (1358848:ℝ)/855161 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84611119:ℝ)/21094400)-4 = (233519:ℝ)/21094400 by norm_num]
    exact paid_middle_461
  · change middlePayment 462 ≤ middleValue ((point 4 cut 1024 462+point 4 cut 1024 463)/2)
    have hp : middlePayment 462 = (643666102566:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 462+point 4 cut 1024 463)/2 = (3384465:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3384465:ℝ)/843776) = (33971200:ℝ)/21378519 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3384465:ℝ)/843776)-4 = (9361:ℝ)/843776 by norm_num]
    exact paid_middle_462
  · change middlePayment 463 ≤ middleValue ((point 4 cut 1024 463+point 4 cut 1024 464)/2)
    have hp : middlePayment 463 = (643705685573:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 463+point 4 cut 1024 464)/2 = (821477:ℝ)/204800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((821477:ℝ)/204800) = (33971200:ℝ)/21378013 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((821477:ℝ)/204800)-4 = (2277:ℝ)/204800 by norm_num]
    exact paid_middle_463
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_028
