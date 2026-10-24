import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints033
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_033 (j : Fin 16) : middlePayment (16*33+j.val) ≤
    middleValue ((point 4 cut 1024 (16*33+j.val)+point 4 cut 1024 (16*33+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 528 ≤ middleValue ((point 4 cut 1024 528+point 4 cut 1024 529)/2)
    have hp : middlePayment 528 = (646281884405:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 528+point 4 cut 1024 529)/2 = (84645021:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84645021:ℝ)/21094400) = (33971200:ℝ)/21345123 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84645021:ℝ)/21094400)-4 = (267421:ℝ)/21094400 by norm_num]
    exact paid_middle_528
  · change middlePayment 529 ≤ middleValue ((point 4 cut 1024 529+point 4 cut 1024 530)/2)
    have hp : middlePayment 529 = (646321569112:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 529+point 4 cut 1024 530)/2 = (84645527:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84645527:ℝ)/21094400) = (33971200:ℝ)/21344617 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84645527:ℝ)/21094400)-4 = (267927:ℝ)/21094400 by norm_num]
    exact paid_middle_529
  · change middlePayment 530 ≤ middleValue ((point 4 cut 1024 530+point 4 cut 1024 531)/2)
    have hp : middlePayment 530 = (646361255361:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 530+point 4 cut 1024 531)/2 = (84646033:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84646033:ℝ)/21094400) = (33971200:ℝ)/21344111 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84646033:ℝ)/21094400)-4 = (268433:ℝ)/21094400 by norm_num]
    exact paid_middle_530
  · change middlePayment 531 ≤ middleValue ((point 4 cut 1024 531+point 4 cut 1024 532)/2)
    have hp : middlePayment 531 = (646400943155:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 531+point 4 cut 1024 532)/2 = (84646539:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84646539:ℝ)/21094400) = (6794240:ℝ)/4268721 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84646539:ℝ)/21094400)-4 = (268939:ℝ)/21094400 by norm_num]
    exact paid_middle_531
  · change middlePayment 532 ≤ middleValue ((point 4 cut 1024 532+point 4 cut 1024 533)/2)
    have hp : middlePayment 532 = (646440632492:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 532+point 4 cut 1024 533)/2 = (16929409:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16929409:ℝ)/4218880) = (33971200:ℝ)/21343099 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16929409:ℝ)/4218880)-4 = (53889:ℝ)/4218880 by norm_num]
    exact paid_middle_532
  · change middlePayment 533 ≤ middleValue ((point 4 cut 1024 533+point 4 cut 1024 534)/2)
    have hp : middlePayment 533 = (646480323373:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 533+point 4 cut 1024 534)/2 = (84647551:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84647551:ℝ)/21094400) = (33971200:ℝ)/21342593 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84647551:ℝ)/21094400)-4 = (269951:ℝ)/21094400 by norm_num]
    exact paid_middle_533
  · change middlePayment 534 ≤ middleValue ((point 4 cut 1024 534+point 4 cut 1024 535)/2)
    have hp : middlePayment 534 = (646520015797:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 534+point 4 cut 1024 535)/2 = (84648057:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84648057:ℝ)/21094400) = (33971200:ℝ)/21342087 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84648057:ℝ)/21094400)-4 = (270457:ℝ)/21094400 by norm_num]
    exact paid_middle_534
  · change middlePayment 535 ≤ middleValue ((point 4 cut 1024 535+point 4 cut 1024 536)/2)
    have hp : middlePayment 535 = (646559709766:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 535+point 4 cut 1024 536)/2 = (84648563:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84648563:ℝ)/21094400) = (33971200:ℝ)/21341581 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84648563:ℝ)/21094400)-4 = (270963:ℝ)/21094400 by norm_num]
    exact paid_middle_535
  · change middlePayment 536 ≤ middleValue ((point 4 cut 1024 536+point 4 cut 1024 537)/2)
    have hp : middlePayment 536 = (646599405278:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 536+point 4 cut 1024 537)/2 = (84649069:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84649069:ℝ)/21094400) = (1358848:ℝ)/853643 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84649069:ℝ)/21094400)-4 = (271469:ℝ)/21094400 by norm_num]
    exact paid_middle_536
  · change middlePayment 537 ≤ middleValue ((point 4 cut 1024 537+point 4 cut 1024 538)/2)
    have hp : middlePayment 537 = (646639102335:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 537+point 4 cut 1024 538)/2 = (3385983:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3385983:ℝ)/843776) = (33971200:ℝ)/21340569 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3385983:ℝ)/843776)-4 = (10879:ℝ)/843776 by norm_num]
    exact paid_middle_537
  · change middlePayment 538 ≤ middleValue ((point 4 cut 1024 538+point 4 cut 1024 539)/2)
    have hp : middlePayment 538 = (646678800936:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 538+point 4 cut 1024 539)/2 = (84650081:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84650081:ℝ)/21094400) = (33971200:ℝ)/21340063 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84650081:ℝ)/21094400)-4 = (272481:ℝ)/21094400 by norm_num]
    exact paid_middle_538
  · change middlePayment 539 ≤ middleValue ((point 4 cut 1024 539+point 4 cut 1024 540)/2)
    have hp : middlePayment 539 = (646718501080:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 539+point 4 cut 1024 540)/2 = (84650587:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84650587:ℝ)/21094400) = (33971200:ℝ)/21339557 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84650587:ℝ)/21094400)-4 = (272987:ℝ)/21094400 by norm_num]
    exact paid_middle_539
  · change middlePayment 540 ≤ middleValue ((point 4 cut 1024 540+point 4 cut 1024 541)/2)
    have hp : middlePayment 540 = (646758202770:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 540+point 4 cut 1024 541)/2 = (84651093:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84651093:ℝ)/21094400) = (33971200:ℝ)/21339051 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84651093:ℝ)/21094400)-4 = (273493:ℝ)/21094400 by norm_num]
    exact paid_middle_540
  · change middlePayment 541 ≤ middleValue ((point 4 cut 1024 541+point 4 cut 1024 542)/2)
    have hp : middlePayment 541 = (646797906003:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 541+point 4 cut 1024 542)/2 = (84651599:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84651599:ℝ)/21094400) = (6794240:ℝ)/4267709 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84651599:ℝ)/21094400)-4 = (273999:ℝ)/21094400 by norm_num]
    exact paid_middle_541
  · change middlePayment 542 ≤ middleValue ((point 4 cut 1024 542+point 4 cut 1024 543)/2)
    have hp : middlePayment 542 = (646837610781:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 542+point 4 cut 1024 543)/2 = (16930421:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16930421:ℝ)/4218880) = (33971200:ℝ)/21338039 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16930421:ℝ)/4218880)-4 = (54901:ℝ)/4218880 by norm_num]
    exact paid_middle_542
  · change middlePayment 543 ≤ middleValue ((point 4 cut 1024 543+point 4 cut 1024 544)/2)
    have hp : middlePayment 543 = (646877317103:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 543+point 4 cut 1024 544)/2 = (84652611:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84652611:ℝ)/21094400) = (33971200:ℝ)/21337533 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84652611:ℝ)/21094400)-4 = (275011:ℝ)/21094400 by norm_num]
    exact paid_middle_543
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_033
