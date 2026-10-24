import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints027
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_027 (j : Fin 16) : middlePayment (16*27+j.val) ≤
    middleValue ((point 4 cut 1024 (16*27+j.val)+point 4 cut 1024 (16*27+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 432 ≤ middleValue ((point 4 cut 1024 432+point 4 cut 1024 433)/2)
    have hp : middlePayment 432 = (642479327301:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 432+point 4 cut 1024 433)/2 = (16919289:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16919289:ℝ)/4218880) = (33971200:ℝ)/21393699 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16919289:ℝ)/4218880)-4 = (43769:ℝ)/4218880 by norm_num]
    exact paid_middle_432
  · change middlePayment 433 ≤ middleValue ((point 4 cut 1024 433+point 4 cut 1024 434)/2)
    have hp : middlePayment 433 = (642518864193:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 433+point 4 cut 1024 434)/2 = (84596951:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84596951:ℝ)/21094400) = (33971200:ℝ)/21393193 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84596951:ℝ)/21094400)-4 = (219351:ℝ)/21094400 by norm_num]
    exact paid_middle_433
  · change middlePayment 434 ≤ middleValue ((point 4 cut 1024 434+point 4 cut 1024 435)/2)
    have hp : middlePayment 434 = (642558402622:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 434+point 4 cut 1024 435)/2 = (84597457:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84597457:ℝ)/21094400) = (33971200:ℝ)/21392687 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84597457:ℝ)/21094400)-4 = (219857:ℝ)/21094400 by norm_num]
    exact paid_middle_434
  · change middlePayment 435 ≤ middleValue ((point 4 cut 1024 435+point 4 cut 1024 436)/2)
    have hp : middlePayment 435 = (642597942586:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 435+point 4 cut 1024 436)/2 = (84597963:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84597963:ℝ)/21094400) = (33971200:ℝ)/21392181 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84597963:ℝ)/21094400)-4 = (220363:ℝ)/21094400 by norm_num]
    exact paid_middle_435
  · change middlePayment 436 ≤ middleValue ((point 4 cut 1024 436+point 4 cut 1024 437)/2)
    have hp : middlePayment 436 = (642637484087:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 436+point 4 cut 1024 437)/2 = (84598469:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84598469:ℝ)/21094400) = (1358848:ℝ)/855667 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84598469:ℝ)/21094400)-4 = (220869:ℝ)/21094400 by norm_num]
    exact paid_middle_436
  · change middlePayment 437 ≤ middleValue ((point 4 cut 1024 437+point 4 cut 1024 438)/2)
    have hp : middlePayment 437 = (642677027124:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 437+point 4 cut 1024 438)/2 = (3383959:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3383959:ℝ)/843776) = (33971200:ℝ)/21391169 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3383959:ℝ)/843776)-4 = (8855:ℝ)/843776 by norm_num]
    exact paid_middle_437
  · change middlePayment 438 ≤ middleValue ((point 4 cut 1024 438+point 4 cut 1024 439)/2)
    have hp : middlePayment 438 = (642716571697:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 438+point 4 cut 1024 439)/2 = (84599481:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84599481:ℝ)/21094400) = (33971200:ℝ)/21390663 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84599481:ℝ)/21094400)-4 = (221881:ℝ)/21094400 by norm_num]
    exact paid_middle_438
  · change middlePayment 439 ≤ middleValue ((point 4 cut 1024 439+point 4 cut 1024 440)/2)
    have hp : middlePayment 439 = (642756117807:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 439+point 4 cut 1024 440)/2 = (84599987:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84599987:ℝ)/21094400) = (33971200:ℝ)/21390157 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84599987:ℝ)/21094400)-4 = (222387:ℝ)/21094400 by norm_num]
    exact paid_middle_439
  · change middlePayment 440 ≤ middleValue ((point 4 cut 1024 440+point 4 cut 1024 441)/2)
    have hp : middlePayment 440 = (642795665454:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 440+point 4 cut 1024 441)/2 = (84600493:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84600493:ℝ)/21094400) = (33971200:ℝ)/21389651 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84600493:ℝ)/21094400)-4 = (222893:ℝ)/21094400 by norm_num]
    exact paid_middle_440
  · change middlePayment 441 ≤ middleValue ((point 4 cut 1024 441+point 4 cut 1024 442)/2)
    have hp : middlePayment 441 = (642835214637:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 441+point 4 cut 1024 442)/2 = (84600999:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84600999:ℝ)/21094400) = (6794240:ℝ)/4277829 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84600999:ℝ)/21094400)-4 = (223399:ℝ)/21094400 by norm_num]
    exact paid_middle_441
  · change middlePayment 442 ≤ middleValue ((point 4 cut 1024 442+point 4 cut 1024 443)/2)
    have hp : middlePayment 442 = (642874765356:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 442+point 4 cut 1024 443)/2 = (16920301:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16920301:ℝ)/4218880) = (33971200:ℝ)/21388639 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16920301:ℝ)/4218880)-4 = (44781:ℝ)/4218880 by norm_num]
    exact paid_middle_442
  · change middlePayment 443 ≤ middleValue ((point 4 cut 1024 443+point 4 cut 1024 444)/2)
    have hp : middlePayment 443 = (642914317612:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 443+point 4 cut 1024 444)/2 = (84602011:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84602011:ℝ)/21094400) = (33971200:ℝ)/21388133 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84602011:ℝ)/21094400)-4 = (224411:ℝ)/21094400 by norm_num]
    exact paid_middle_443
  · change middlePayment 444 ≤ middleValue ((point 4 cut 1024 444+point 4 cut 1024 445)/2)
    have hp : middlePayment 444 = (642953871406:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 444+point 4 cut 1024 445)/2 = (84602517:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84602517:ℝ)/21094400) = (33971200:ℝ)/21387627 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84602517:ℝ)/21094400)-4 = (224917:ℝ)/21094400 by norm_num]
    exact paid_middle_444
  · change middlePayment 445 ≤ middleValue ((point 4 cut 1024 445+point 4 cut 1024 446)/2)
    have hp : middlePayment 445 = (642993426736:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 445+point 4 cut 1024 446)/2 = (84603023:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84603023:ℝ)/21094400) = (33971200:ℝ)/21387121 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84603023:ℝ)/21094400)-4 = (225423:ℝ)/21094400 by norm_num]
    exact paid_middle_445
  · change middlePayment 446 ≤ middleValue ((point 4 cut 1024 446+point 4 cut 1024 447)/2)
    have hp : middlePayment 446 = (643032983603:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 446+point 4 cut 1024 447)/2 = (84603529:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84603529:ℝ)/21094400) = (6794240:ℝ)/4277323 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84603529:ℝ)/21094400)-4 = (225929:ℝ)/21094400 by norm_num]
    exact paid_middle_446
  · change middlePayment 447 ≤ middleValue ((point 4 cut 1024 447+point 4 cut 1024 448)/2)
    have hp : middlePayment 447 = (643072542007:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 447+point 4 cut 1024 448)/2 = (16920807:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16920807:ℝ)/4218880) = (33971200:ℝ)/21386109 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16920807:ℝ)/4218880)-4 = (45287:ℝ)/4218880 by norm_num]
    exact paid_middle_447
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_027
