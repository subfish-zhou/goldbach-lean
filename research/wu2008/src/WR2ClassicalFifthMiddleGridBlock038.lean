import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints038
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_038 (j : Fin 16) : middlePayment (16*38+j.val) ≤
    middleValue ((point 4 cut 1024 (16*38+j.val)+point 4 cut 1024 (16*38+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 608 ≤ middleValue ((point 4 cut 1024 608+point 4 cut 1024 609)/2)
    have hp : middlePayment 608 = (649461544796:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 608+point 4 cut 1024 609)/2 = (84685501:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84685501:ℝ)/21094400) = (33971200:ℝ)/21304643 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84685501:ℝ)/21094400)-4 = (307901:ℝ)/21094400 by norm_num]
    exact paid_middle_608
  · change middlePayment 609 ≤ middleValue ((point 4 cut 1024 609+point 4 cut 1024 610)/2)
    have hp : middlePayment 609 = (649501353229:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 609+point 4 cut 1024 610)/2 = (84686007:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84686007:ℝ)/21094400) = (33971200:ℝ)/21304137 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84686007:ℝ)/21094400)-4 = (308407:ℝ)/21094400 by norm_num]
    exact paid_middle_609
  · change middlePayment 610 ≤ middleValue ((point 4 cut 1024 610+point 4 cut 1024 611)/2)
    have hp : middlePayment 610 = (649541163212:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 610+point 4 cut 1024 611)/2 = (84686513:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84686513:ℝ)/21094400) = (33971200:ℝ)/21303631 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84686513:ℝ)/21094400)-4 = (308913:ℝ)/21094400 by norm_num]
    exact paid_middle_610
  · change middlePayment 611 ≤ middleValue ((point 4 cut 1024 611+point 4 cut 1024 612)/2)
    have hp : middlePayment 611 = (649580974745:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 611+point 4 cut 1024 612)/2 = (84687019:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84687019:ℝ)/21094400) = (1358848:ℝ)/852125 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84687019:ℝ)/21094400)-4 = (309419:ℝ)/21094400 by norm_num]
    exact paid_middle_611
  · change middlePayment 612 ≤ middleValue ((point 4 cut 1024 612+point 4 cut 1024 613)/2)
    have hp : middlePayment 612 = (649620787828:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 612+point 4 cut 1024 613)/2 = (3387501:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3387501:ℝ)/843776) = (33971200:ℝ)/21302619 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3387501:ℝ)/843776)-4 = (12397:ℝ)/843776 by norm_num]
    exact paid_middle_612
  · change middlePayment 613 ≤ middleValue ((point 4 cut 1024 613+point 4 cut 1024 614)/2)
    have hp : middlePayment 613 = (649660602461:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 613+point 4 cut 1024 614)/2 = (84688031:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84688031:ℝ)/21094400) = (33971200:ℝ)/21302113 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84688031:ℝ)/21094400)-4 = (310431:ℝ)/21094400 by norm_num]
    exact paid_middle_613
  · change middlePayment 614 ≤ middleValue ((point 4 cut 1024 614+point 4 cut 1024 615)/2)
    have hp : middlePayment 614 = (649700418644:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 614+point 4 cut 1024 615)/2 = (84688537:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84688537:ℝ)/21094400) = (33971200:ℝ)/21301607 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84688537:ℝ)/21094400)-4 = (310937:ℝ)/21094400 by norm_num]
    exact paid_middle_614
  · change middlePayment 615 ≤ middleValue ((point 4 cut 1024 615+point 4 cut 1024 616)/2)
    have hp : middlePayment 615 = (649740236377:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 615+point 4 cut 1024 616)/2 = (84689043:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84689043:ℝ)/21094400) = (33971200:ℝ)/21301101 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84689043:ℝ)/21094400)-4 = (311443:ℝ)/21094400 by norm_num]
    exact paid_middle_615
  · change middlePayment 616 ≤ middleValue ((point 4 cut 1024 616+point 4 cut 1024 617)/2)
    have hp : middlePayment 616 = (649780055661:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 616+point 4 cut 1024 617)/2 = (84689549:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84689549:ℝ)/21094400) = (6794240:ℝ)/4260119 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84689549:ℝ)/21094400)-4 = (311949:ℝ)/21094400 by norm_num]
    exact paid_middle_616
  · change middlePayment 617 ≤ middleValue ((point 4 cut 1024 617+point 4 cut 1024 618)/2)
    have hp : middlePayment 617 = (649819876495:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 617+point 4 cut 1024 618)/2 = (16938011:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16938011:ℝ)/4218880) = (33971200:ℝ)/21300089 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16938011:ℝ)/4218880)-4 = (62491:ℝ)/4218880 by norm_num]
    exact paid_middle_617
  · change middlePayment 618 ≤ middleValue ((point 4 cut 1024 618+point 4 cut 1024 619)/2)
    have hp : middlePayment 618 = (649859698879:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 618+point 4 cut 1024 619)/2 = (84690561:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84690561:ℝ)/21094400) = (33971200:ℝ)/21299583 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84690561:ℝ)/21094400)-4 = (312961:ℝ)/21094400 by norm_num]
    exact paid_middle_618
  · change middlePayment 619 ≤ middleValue ((point 4 cut 1024 619+point 4 cut 1024 620)/2)
    have hp : middlePayment 619 = (649899522813:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 619+point 4 cut 1024 620)/2 = (84691067:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84691067:ℝ)/21094400) = (33971200:ℝ)/21299077 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84691067:ℝ)/21094400)-4 = (313467:ℝ)/21094400 by norm_num]
    exact paid_middle_619
  · change middlePayment 620 ≤ middleValue ((point 4 cut 1024 620+point 4 cut 1024 621)/2)
    have hp : middlePayment 620 = (649939348298:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 620+point 4 cut 1024 621)/2 = (84691573:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84691573:ℝ)/21094400) = (33971200:ℝ)/21298571 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84691573:ℝ)/21094400)-4 = (313973:ℝ)/21094400 by norm_num]
    exact paid_middle_620
  · change middlePayment 621 ≤ middleValue ((point 4 cut 1024 621+point 4 cut 1024 622)/2)
    have hp : middlePayment 621 = (649979175334:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 621+point 4 cut 1024 622)/2 = (84692079:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84692079:ℝ)/21094400) = (6794240:ℝ)/4259613 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84692079:ℝ)/21094400)-4 = (314479:ℝ)/21094400 by norm_num]
    exact paid_middle_621
  · change middlePayment 622 ≤ middleValue ((point 4 cut 1024 622+point 4 cut 1024 623)/2)
    have hp : middlePayment 622 = (650019003921:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 622+point 4 cut 1024 623)/2 = (16938517:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16938517:ℝ)/4218880) = (33971200:ℝ)/21297559 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16938517:ℝ)/4218880)-4 = (62997:ℝ)/4218880 by norm_num]
    exact paid_middle_622
  · change middlePayment 623 ≤ middleValue ((point 4 cut 1024 623+point 4 cut 1024 624)/2)
    have hp : middlePayment 623 = (650058834058:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 623+point 4 cut 1024 624)/2 = (84693091:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84693091:ℝ)/21094400) = (33971200:ℝ)/21297053 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84693091:ℝ)/21094400)-4 = (315491:ℝ)/21094400 by norm_num]
    exact paid_middle_623
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_038
