import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints032
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_032 (j : Fin 16) : middlePayment (16*32+j.val) ≤
    middleValue ((point 4 cut 1024 (16*32+j.val)+point 4 cut 1024 (16*32+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 512 ≤ middleValue ((point 4 cut 1024 512+point 4 cut 1024 513)/2)
    have hp : middlePayment 512 = (645647138957:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 512+point 4 cut 1024 513)/2 = (3385477:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3385477:ℝ)/843776) = (33971200:ℝ)/21353219 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3385477:ℝ)/843776)-4 = (10373:ℝ)/843776 by norm_num]
    exact paid_middle_512
  · change middlePayment 513 ≤ middleValue ((point 4 cut 1024 513+point 4 cut 1024 514)/2)
    have hp : middlePayment 513 = (645686798977:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 513+point 4 cut 1024 514)/2 = (84637431:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84637431:ℝ)/21094400) = (33971200:ℝ)/21352713 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84637431:ℝ)/21094400)-4 = (259831:ℝ)/21094400 by norm_num]
    exact paid_middle_513
  · change middlePayment 514 ≤ middleValue ((point 4 cut 1024 514+point 4 cut 1024 515)/2)
    have hp : middlePayment 514 = (645726460541:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 514+point 4 cut 1024 515)/2 = (84637937:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84637937:ℝ)/21094400) = (33971200:ℝ)/21352207 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84637937:ℝ)/21094400)-4 = (260337:ℝ)/21094400 by norm_num]
    exact paid_middle_514
  · change middlePayment 515 ≤ middleValue ((point 4 cut 1024 515+point 4 cut 1024 516)/2)
    have hp : middlePayment 515 = (645766123646:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 515+point 4 cut 1024 516)/2 = (84638443:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84638443:ℝ)/21094400) = (33971200:ℝ)/21351701 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84638443:ℝ)/21094400)-4 = (260843:ℝ)/21094400 by norm_num]
    exact paid_middle_515
  · change middlePayment 516 ≤ middleValue ((point 4 cut 1024 516+point 4 cut 1024 517)/2)
    have hp : middlePayment 516 = (645805788294:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 516+point 4 cut 1024 517)/2 = (84638949:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84638949:ℝ)/21094400) = (6794240:ℝ)/4270239 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84638949:ℝ)/21094400)-4 = (261349:ℝ)/21094400 by norm_num]
    exact paid_middle_516
  · change middlePayment 517 ≤ middleValue ((point 4 cut 1024 517+point 4 cut 1024 518)/2)
    have hp : middlePayment 517 = (645845454484:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 517+point 4 cut 1024 518)/2 = (16927891:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16927891:ℝ)/4218880) = (33971200:ℝ)/21350689 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16927891:ℝ)/4218880)-4 = (52371:ℝ)/4218880 by norm_num]
    exact paid_middle_517
  · change middlePayment 518 ≤ middleValue ((point 4 cut 1024 518+point 4 cut 1024 519)/2)
    have hp : middlePayment 518 = (645885122217:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 518+point 4 cut 1024 519)/2 = (84639961:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84639961:ℝ)/21094400) = (33971200:ℝ)/21350183 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84639961:ℝ)/21094400)-4 = (262361:ℝ)/21094400 by norm_num]
    exact paid_middle_518
  · change middlePayment 519 ≤ middleValue ((point 4 cut 1024 519+point 4 cut 1024 520)/2)
    have hp : middlePayment 519 = (645924791493:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 519+point 4 cut 1024 520)/2 = (84640467:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84640467:ℝ)/21094400) = (33971200:ℝ)/21349677 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84640467:ℝ)/21094400)-4 = (262867:ℝ)/21094400 by norm_num]
    exact paid_middle_519
  · change middlePayment 520 ≤ middleValue ((point 4 cut 1024 520+point 4 cut 1024 521)/2)
    have hp : middlePayment 520 = (645964462311:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 520+point 4 cut 1024 521)/2 = (84640973:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84640973:ℝ)/21094400) = (33971200:ℝ)/21349171 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84640973:ℝ)/21094400)-4 = (263373:ℝ)/21094400 by norm_num]
    exact paid_middle_520
  · change middlePayment 521 ≤ middleValue ((point 4 cut 1024 521+point 4 cut 1024 522)/2)
    have hp : middlePayment 521 = (646004134672:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 521+point 4 cut 1024 522)/2 = (84641479:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84641479:ℝ)/21094400) = (6794240:ℝ)/4269733 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84641479:ℝ)/21094400)-4 = (263879:ℝ)/21094400 by norm_num]
    exact paid_middle_521
  · change middlePayment 522 ≤ middleValue ((point 4 cut 1024 522+point 4 cut 1024 523)/2)
    have hp : middlePayment 522 = (646043808576:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 522+point 4 cut 1024 523)/2 = (16928397:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16928397:ℝ)/4218880) = (33971200:ℝ)/21348159 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16928397:ℝ)/4218880)-4 = (52877:ℝ)/4218880 by norm_num]
    exact paid_middle_522
  · change middlePayment 523 ≤ middleValue ((point 4 cut 1024 523+point 4 cut 1024 524)/2)
    have hp : middlePayment 523 = (646083484023:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 523+point 4 cut 1024 524)/2 = (84642491:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84642491:ℝ)/21094400) = (33971200:ℝ)/21347653 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84642491:ℝ)/21094400)-4 = (264891:ℝ)/21094400 by norm_num]
    exact paid_middle_523
  · change middlePayment 524 ≤ middleValue ((point 4 cut 1024 524+point 4 cut 1024 525)/2)
    have hp : middlePayment 524 = (646123161013:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 524+point 4 cut 1024 525)/2 = (84642997:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84642997:ℝ)/21094400) = (33971200:ℝ)/21347147 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84642997:ℝ)/21094400)-4 = (265397:ℝ)/21094400 by norm_num]
    exact paid_middle_524
  · change middlePayment 525 ≤ middleValue ((point 4 cut 1024 525+point 4 cut 1024 526)/2)
    have hp : middlePayment 525 = (646162839546:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 525+point 4 cut 1024 526)/2 = (84643503:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84643503:ℝ)/21094400) = (33971200:ℝ)/21346641 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84643503:ℝ)/21094400)-4 = (265903:ℝ)/21094400 by norm_num]
    exact paid_middle_525
  · change middlePayment 526 ≤ middleValue ((point 4 cut 1024 526+point 4 cut 1024 527)/2)
    have hp : middlePayment 526 = (646202519623:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 526+point 4 cut 1024 527)/2 = (84644009:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84644009:ℝ)/21094400) = (6794240:ℝ)/4269227 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84644009:ℝ)/21094400)-4 = (266409:ℝ)/21094400 by norm_num]
    exact paid_middle_526
  · change middlePayment 527 ≤ middleValue ((point 4 cut 1024 527+point 4 cut 1024 528)/2)
    have hp : middlePayment 527 = (646242201242:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 527+point 4 cut 1024 528)/2 = (16928903:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16928903:ℝ)/4218880) = (33971200:ℝ)/21345629 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16928903:ℝ)/4218880)-4 = (53383:ℝ)/4218880 by norm_num]
    exact paid_middle_527
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_032
