import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints034
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_034 (j : Fin 16) : middlePayment (16*34+j.val) ≤
    middleValue ((point 4 cut 1024 (16*34+j.val)+point 4 cut 1024 (16*34+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 544 ≤ middleValue ((point 4 cut 1024 544+point 4 cut 1024 545)/2)
    have hp : middlePayment 544 = (646917024970:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 544+point 4 cut 1024 545)/2 = (84653117:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84653117:ℝ)/21094400) = (33971200:ℝ)/21337027 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84653117:ℝ)/21094400)-4 = (275517:ℝ)/21094400 by norm_num]
    exact paid_middle_544
  · change middlePayment 545 ≤ middleValue ((point 4 cut 1024 545+point 4 cut 1024 546)/2)
    have hp : middlePayment 545 = (646956734382:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 545+point 4 cut 1024 546)/2 = (84653623:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84653623:ℝ)/21094400) = (33971200:ℝ)/21336521 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84653623:ℝ)/21094400)-4 = (276023:ℝ)/21094400 by norm_num]
    exact paid_middle_545
  · change middlePayment 546 ≤ middleValue ((point 4 cut 1024 546+point 4 cut 1024 547)/2)
    have hp : middlePayment 546 = (646996445339:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 546+point 4 cut 1024 547)/2 = (84654129:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84654129:ℝ)/21094400) = (6794240:ℝ)/4267203 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84654129:ℝ)/21094400)-4 = (276529:ℝ)/21094400 by norm_num]
    exact paid_middle_546
  · change middlePayment 547 ≤ middleValue ((point 4 cut 1024 547+point 4 cut 1024 548)/2)
    have hp : middlePayment 547 = (647036157840:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 547+point 4 cut 1024 548)/2 = (16930927:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16930927:ℝ)/4218880) = (33971200:ℝ)/21335509 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16930927:ℝ)/4218880)-4 = (55407:ℝ)/4218880 by norm_num]
    exact paid_middle_547
  · change middlePayment 548 ≤ middleValue ((point 4 cut 1024 548+point 4 cut 1024 549)/2)
    have hp : middlePayment 548 = (647075871886:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 548+point 4 cut 1024 549)/2 = (84655141:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84655141:ℝ)/21094400) = (33971200:ℝ)/21335003 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84655141:ℝ)/21094400)-4 = (277541:ℝ)/21094400 by norm_num]
    exact paid_middle_548
  · change middlePayment 549 ≤ middleValue ((point 4 cut 1024 549+point 4 cut 1024 550)/2)
    have hp : middlePayment 549 = (647115587477:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 549+point 4 cut 1024 550)/2 = (84655647:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84655647:ℝ)/21094400) = (33971200:ℝ)/21334497 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84655647:ℝ)/21094400)-4 = (278047:ℝ)/21094400 by norm_num]
    exact paid_middle_549
  · change middlePayment 550 ≤ middleValue ((point 4 cut 1024 550+point 4 cut 1024 551)/2)
    have hp : middlePayment 550 = (647155304614:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 550+point 4 cut 1024 551)/2 = (84656153:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84656153:ℝ)/21094400) = (33971200:ℝ)/21333991 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84656153:ℝ)/21094400)-4 = (278553:ℝ)/21094400 by norm_num]
    exact paid_middle_550
  · change middlePayment 551 ≤ middleValue ((point 4 cut 1024 551+point 4 cut 1024 552)/2)
    have hp : middlePayment 551 = (647195023295:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 551+point 4 cut 1024 552)/2 = (84656659:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84656659:ℝ)/21094400) = (6794240:ℝ)/4266697 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84656659:ℝ)/21094400)-4 = (279059:ℝ)/21094400 by norm_num]
    exact paid_middle_551
  · change middlePayment 552 ≤ middleValue ((point 4 cut 1024 552+point 4 cut 1024 553)/2)
    have hp : middlePayment 552 = (647234743522:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 552+point 4 cut 1024 553)/2 = (16931433:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16931433:ℝ)/4218880) = (33971200:ℝ)/21332979 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16931433:ℝ)/4218880)-4 = (55913:ℝ)/4218880 by norm_num]
    exact paid_middle_552
  · change middlePayment 553 ≤ middleValue ((point 4 cut 1024 553+point 4 cut 1024 554)/2)
    have hp : middlePayment 553 = (647274465294:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 553+point 4 cut 1024 554)/2 = (84657671:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84657671:ℝ)/21094400) = (33971200:ℝ)/21332473 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84657671:ℝ)/21094400)-4 = (280071:ℝ)/21094400 by norm_num]
    exact paid_middle_553
  · change middlePayment 554 ≤ middleValue ((point 4 cut 1024 554+point 4 cut 1024 555)/2)
    have hp : middlePayment 554 = (647314188611:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 554+point 4 cut 1024 555)/2 = (84658177:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84658177:ℝ)/21094400) = (33971200:ℝ)/21331967 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84658177:ℝ)/21094400)-4 = (280577:ℝ)/21094400 by norm_num]
    exact paid_middle_554
  · change middlePayment 555 ≤ middleValue ((point 4 cut 1024 555+point 4 cut 1024 556)/2)
    have hp : middlePayment 555 = (647353913474:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 555+point 4 cut 1024 556)/2 = (84658683:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84658683:ℝ)/21094400) = (33971200:ℝ)/21331461 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84658683:ℝ)/21094400)-4 = (281083:ℝ)/21094400 by norm_num]
    exact paid_middle_555
  · change middlePayment 556 ≤ middleValue ((point 4 cut 1024 556+point 4 cut 1024 557)/2)
    have hp : middlePayment 556 = (647393639882:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 556+point 4 cut 1024 557)/2 = (84659189:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84659189:ℝ)/21094400) = (6794240:ℝ)/4266191 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84659189:ℝ)/21094400)-4 = (281589:ℝ)/21094400 by norm_num]
    exact paid_middle_556
  · change middlePayment 557 ≤ middleValue ((point 4 cut 1024 557+point 4 cut 1024 558)/2)
    have hp : middlePayment 557 = (647433367836:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 557+point 4 cut 1024 558)/2 = (16931939:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16931939:ℝ)/4218880) = (33971200:ℝ)/21330449 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16931939:ℝ)/4218880)-4 = (56419:ℝ)/4218880 by norm_num]
    exact paid_middle_557
  · change middlePayment 558 ≤ middleValue ((point 4 cut 1024 558+point 4 cut 1024 559)/2)
    have hp : middlePayment 558 = (647473097335:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 558+point 4 cut 1024 559)/2 = (84660201:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84660201:ℝ)/21094400) = (33971200:ℝ)/21329943 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84660201:ℝ)/21094400)-4 = (282601:ℝ)/21094400 by norm_num]
    exact paid_middle_558
  · change middlePayment 559 ≤ middleValue ((point 4 cut 1024 559+point 4 cut 1024 560)/2)
    have hp : middlePayment 559 = (647512828381:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 559+point 4 cut 1024 560)/2 = (84660707:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84660707:ℝ)/21094400) = (33971200:ℝ)/21329437 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84660707:ℝ)/21094400)-4 = (283107:ℝ)/21094400 by norm_num]
    exact paid_middle_559
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_034
