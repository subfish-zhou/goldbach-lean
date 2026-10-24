import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints030
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_030 (j : Fin 16) : middlePayment (16*30+j.val) ≤
    middleValue ((point 4 cut 1024 (16*30+j.val)+point 4 cut 1024 (16*30+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 480 ≤ middleValue ((point 4 cut 1024 480+point 4 cut 1024 481)/2)
    have hp : middlePayment 480 = (644378832132:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 480+point 4 cut 1024 481)/2 = (84620733:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84620733:ℝ)/21094400) = (33971200:ℝ)/21369411 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84620733:ℝ)/21094400)-4 = (243133:ℝ)/21094400 by norm_num]
    exact paid_middle_480
  · change middlePayment 481 ≤ middleValue ((point 4 cut 1024 481+point 4 cut 1024 482)/2)
    have hp : middlePayment 481 = (644418442842:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 481+point 4 cut 1024 482)/2 = (84621239:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84621239:ℝ)/21094400) = (6794240:ℝ)/4273781 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84621239:ℝ)/21094400)-4 = (243639:ℝ)/21094400 by norm_num]
    exact paid_middle_481
  · change middlePayment 482 ≤ middleValue ((point 4 cut 1024 482+point 4 cut 1024 483)/2)
    have hp : middlePayment 482 = (644458055092:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 482+point 4 cut 1024 483)/2 = (16924349:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16924349:ℝ)/4218880) = (33971200:ℝ)/21368399 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16924349:ℝ)/4218880)-4 = (48829:ℝ)/4218880 by norm_num]
    exact paid_middle_482
  · change middlePayment 483 ≤ middleValue ((point 4 cut 1024 483+point 4 cut 1024 484)/2)
    have hp : middlePayment 483 = (644497668881:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 483+point 4 cut 1024 484)/2 = (84622251:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84622251:ℝ)/21094400) = (33971200:ℝ)/21367893 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84622251:ℝ)/21094400)-4 = (244651:ℝ)/21094400 by norm_num]
    exact paid_middle_483
  · change middlePayment 484 ≤ middleValue ((point 4 cut 1024 484+point 4 cut 1024 485)/2)
    have hp : middlePayment 484 = (644537284210:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 484+point 4 cut 1024 485)/2 = (84622757:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84622757:ℝ)/21094400) = (33971200:ℝ)/21367387 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84622757:ℝ)/21094400)-4 = (245157:ℝ)/21094400 by norm_num]
    exact paid_middle_484
  · change middlePayment 485 ≤ middleValue ((point 4 cut 1024 485+point 4 cut 1024 486)/2)
    have hp : middlePayment 485 = (644576901080:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 485+point 4 cut 1024 486)/2 = (84623263:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84623263:ℝ)/21094400) = (33971200:ℝ)/21366881 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84623263:ℝ)/21094400)-4 = (245663:ℝ)/21094400 by norm_num]
    exact paid_middle_485
  · change middlePayment 486 ≤ middleValue ((point 4 cut 1024 486+point 4 cut 1024 487)/2)
    have hp : middlePayment 486 = (644616519489:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 486+point 4 cut 1024 487)/2 = (84623769:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84623769:ℝ)/21094400) = (1358848:ℝ)/854655 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84623769:ℝ)/21094400)-4 = (246169:ℝ)/21094400 by norm_num]
    exact paid_middle_486
  · change middlePayment 487 ≤ middleValue ((point 4 cut 1024 487+point 4 cut 1024 488)/2)
    have hp : middlePayment 487 = (644656139439:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 487+point 4 cut 1024 488)/2 = (3384971:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3384971:ℝ)/843776) = (33971200:ℝ)/21365869 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3384971:ℝ)/843776)-4 = (9867:ℝ)/843776 by norm_num]
    exact paid_middle_487
  · change middlePayment 488 ≤ middleValue ((point 4 cut 1024 488+point 4 cut 1024 489)/2)
    have hp : middlePayment 488 = (644695760929:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 488+point 4 cut 1024 489)/2 = (84624781:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84624781:ℝ)/21094400) = (33971200:ℝ)/21365363 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84624781:ℝ)/21094400)-4 = (247181:ℝ)/21094400 by norm_num]
    exact paid_middle_488
  · change middlePayment 489 ≤ middleValue ((point 4 cut 1024 489+point 4 cut 1024 490)/2)
    have hp : middlePayment 489 = (644735383959:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 489+point 4 cut 1024 490)/2 = (84625287:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84625287:ℝ)/21094400) = (33971200:ℝ)/21364857 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84625287:ℝ)/21094400)-4 = (247687:ℝ)/21094400 by norm_num]
    exact paid_middle_489
  · change middlePayment 490 ≤ middleValue ((point 4 cut 1024 490+point 4 cut 1024 491)/2)
    have hp : middlePayment 490 = (644775008529:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 490+point 4 cut 1024 491)/2 = (84625793:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84625793:ℝ)/21094400) = (33971200:ℝ)/21364351 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84625793:ℝ)/21094400)-4 = (248193:ℝ)/21094400 by norm_num]
    exact paid_middle_490
  · change middlePayment 491 ≤ middleValue ((point 4 cut 1024 491+point 4 cut 1024 492)/2)
    have hp : middlePayment 491 = (644814634640:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 491+point 4 cut 1024 492)/2 = (84626299:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84626299:ℝ)/21094400) = (6794240:ℝ)/4272769 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84626299:ℝ)/21094400)-4 = (248699:ℝ)/21094400 by norm_num]
    exact paid_middle_491
  · change middlePayment 492 ≤ middleValue ((point 4 cut 1024 492+point 4 cut 1024 493)/2)
    have hp : middlePayment 492 = (644854262292:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 492+point 4 cut 1024 493)/2 = (16925361:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16925361:ℝ)/4218880) = (33971200:ℝ)/21363339 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16925361:ℝ)/4218880)-4 = (49841:ℝ)/4218880 by norm_num]
    exact paid_middle_492
  · change middlePayment 493 ≤ middleValue ((point 4 cut 1024 493+point 4 cut 1024 494)/2)
    have hp : middlePayment 493 = (644893891484:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 493+point 4 cut 1024 494)/2 = (84627311:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84627311:ℝ)/21094400) = (33971200:ℝ)/21362833 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84627311:ℝ)/21094400)-4 = (249711:ℝ)/21094400 by norm_num]
    exact paid_middle_493
  · change middlePayment 494 ≤ middleValue ((point 4 cut 1024 494+point 4 cut 1024 495)/2)
    have hp : middlePayment 494 = (644933522217:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 494+point 4 cut 1024 495)/2 = (84627817:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84627817:ℝ)/21094400) = (33971200:ℝ)/21362327 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84627817:ℝ)/21094400)-4 = (250217:ℝ)/21094400 by norm_num]
    exact paid_middle_494
  · change middlePayment 495 ≤ middleValue ((point 4 cut 1024 495+point 4 cut 1024 496)/2)
    have hp : middlePayment 495 = (644973154491:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 495+point 4 cut 1024 496)/2 = (84628323:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84628323:ℝ)/21094400) = (33971200:ℝ)/21361821 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84628323:ℝ)/21094400)-4 = (250723:ℝ)/21094400 by norm_num]
    exact paid_middle_495
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_030
