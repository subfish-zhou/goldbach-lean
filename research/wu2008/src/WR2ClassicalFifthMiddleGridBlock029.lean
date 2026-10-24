import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints029
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_029 (j : Fin 16) : middlePayment (16*29+j.val) ≤
    middleValue ((point 4 cut 1024 (16*29+j.val)+point 4 cut 1024 (16*29+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 464 ≤ middleValue ((point 4 cut 1024 464+point 4 cut 1024 465)/2)
    have hp : middlePayment 464 = (643745270119:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 464+point 4 cut 1024 465)/2 = (84612637:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84612637:ℝ)/21094400) = (33971200:ℝ)/21377507 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84612637:ℝ)/21094400)-4 = (235037:ℝ)/21094400 by norm_num]
    exact paid_middle_464
  · change middlePayment 465 ≤ middleValue ((point 4 cut 1024 465+point 4 cut 1024 466)/2)
    have hp : middlePayment 465 = (643784856203:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 465+point 4 cut 1024 466)/2 = (84613143:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84613143:ℝ)/21094400) = (33971200:ℝ)/21377001 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84613143:ℝ)/21094400)-4 = (235543:ℝ)/21094400 by norm_num]
    exact paid_middle_465
  · change middlePayment 466 ≤ middleValue ((point 4 cut 1024 466+point 4 cut 1024 467)/2)
    have hp : middlePayment 466 = (643824443826:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 466+point 4 cut 1024 467)/2 = (84613649:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84613649:ℝ)/21094400) = (6794240:ℝ)/4275299 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84613649:ℝ)/21094400)-4 = (236049:ℝ)/21094400 by norm_num]
    exact paid_middle_466
  · change middlePayment 467 ≤ middleValue ((point 4 cut 1024 467+point 4 cut 1024 468)/2)
    have hp : middlePayment 467 = (643864032987:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 467+point 4 cut 1024 468)/2 = (16922831:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16922831:ℝ)/4218880) = (33971200:ℝ)/21375989 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16922831:ℝ)/4218880)-4 = (47311:ℝ)/4218880 by norm_num]
    exact paid_middle_467
  · change middlePayment 468 ≤ middleValue ((point 4 cut 1024 468+point 4 cut 1024 469)/2)
    have hp : middlePayment 468 = (643903623687:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 468+point 4 cut 1024 469)/2 = (84614661:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84614661:ℝ)/21094400) = (33971200:ℝ)/21375483 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84614661:ℝ)/21094400)-4 = (237061:ℝ)/21094400 by norm_num]
    exact paid_middle_468
  · change middlePayment 469 ≤ middleValue ((point 4 cut 1024 469+point 4 cut 1024 470)/2)
    have hp : middlePayment 469 = (643943215926:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 469+point 4 cut 1024 470)/2 = (84615167:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84615167:ℝ)/21094400) = (33971200:ℝ)/21374977 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84615167:ℝ)/21094400)-4 = (237567:ℝ)/21094400 by norm_num]
    exact paid_middle_469
  · change middlePayment 470 ≤ middleValue ((point 4 cut 1024 470+point 4 cut 1024 471)/2)
    have hp : middlePayment 470 = (643982809704:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 470+point 4 cut 1024 471)/2 = (84615673:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84615673:ℝ)/21094400) = (33971200:ℝ)/21374471 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84615673:ℝ)/21094400)-4 = (238073:ℝ)/21094400 by norm_num]
    exact paid_middle_470
  · change middlePayment 471 ≤ middleValue ((point 4 cut 1024 471+point 4 cut 1024 472)/2)
    have hp : middlePayment 471 = (644022405020:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 471+point 4 cut 1024 472)/2 = (84616179:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84616179:ℝ)/21094400) = (6794240:ℝ)/4274793 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84616179:ℝ)/21094400)-4 = (238579:ℝ)/21094400 by norm_num]
    exact paid_middle_471
  · change middlePayment 472 ≤ middleValue ((point 4 cut 1024 472+point 4 cut 1024 473)/2)
    have hp : middlePayment 472 = (644062001876:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 472+point 4 cut 1024 473)/2 = (16923337:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16923337:ℝ)/4218880) = (33971200:ℝ)/21373459 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16923337:ℝ)/4218880)-4 = (47817:ℝ)/4218880 by norm_num]
    exact paid_middle_472
  · change middlePayment 473 ≤ middleValue ((point 4 cut 1024 473+point 4 cut 1024 474)/2)
    have hp : middlePayment 473 = (644101600270:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 473+point 4 cut 1024 474)/2 = (84617191:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84617191:ℝ)/21094400) = (33971200:ℝ)/21372953 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84617191:ℝ)/21094400)-4 = (239591:ℝ)/21094400 by norm_num]
    exact paid_middle_473
  · change middlePayment 474 ≤ middleValue ((point 4 cut 1024 474+point 4 cut 1024 475)/2)
    have hp : middlePayment 474 = (644141200204:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 474+point 4 cut 1024 475)/2 = (84617697:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84617697:ℝ)/21094400) = (33971200:ℝ)/21372447 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84617697:ℝ)/21094400)-4 = (240097:ℝ)/21094400 by norm_num]
    exact paid_middle_474
  · change middlePayment 475 ≤ middleValue ((point 4 cut 1024 475+point 4 cut 1024 476)/2)
    have hp : middlePayment 475 = (644180801677:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 475+point 4 cut 1024 476)/2 = (84618203:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84618203:ℝ)/21094400) = (33971200:ℝ)/21371941 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84618203:ℝ)/21094400)-4 = (240603:ℝ)/21094400 by norm_num]
    exact paid_middle_475
  · change middlePayment 476 ≤ middleValue ((point 4 cut 1024 476+point 4 cut 1024 477)/2)
    have hp : middlePayment 476 = (644220404689:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 476+point 4 cut 1024 477)/2 = (84618709:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84618709:ℝ)/21094400) = (6794240:ℝ)/4274287 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84618709:ℝ)/21094400)-4 = (241109:ℝ)/21094400 by norm_num]
    exact paid_middle_476
  · change middlePayment 477 ≤ middleValue ((point 4 cut 1024 477+point 4 cut 1024 478)/2)
    have hp : middlePayment 477 = (644260009240:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 477+point 4 cut 1024 478)/2 = (16923843:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16923843:ℝ)/4218880) = (33971200:ℝ)/21370929 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16923843:ℝ)/4218880)-4 = (48323:ℝ)/4218880 by norm_num]
    exact paid_middle_477
  · change middlePayment 478 ≤ middleValue ((point 4 cut 1024 478+point 4 cut 1024 479)/2)
    have hp : middlePayment 478 = (644299615331:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 478+point 4 cut 1024 479)/2 = (84619721:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84619721:ℝ)/21094400) = (33971200:ℝ)/21370423 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84619721:ℝ)/21094400)-4 = (242121:ℝ)/21094400 by norm_num]
    exact paid_middle_478
  · change middlePayment 479 ≤ middleValue ((point 4 cut 1024 479+point 4 cut 1024 480)/2)
    have hp : middlePayment 479 = (644339222962:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 479+point 4 cut 1024 480)/2 = (84620227:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84620227:ℝ)/21094400) = (33971200:ℝ)/21369917 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84620227:ℝ)/21094400)-4 = (242627:ℝ)/21094400 by norm_num]
    exact paid_middle_479
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_029
