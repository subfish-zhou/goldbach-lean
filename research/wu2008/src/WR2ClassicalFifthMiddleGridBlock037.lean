import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints037
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_037 (j : Fin 16) : middlePayment (16*37+j.val) ≤
    middleValue ((point 4 cut 1024 (16*37+j.val)+point 4 cut 1024 (16*37+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 592 ≤ middleValue ((point 4 cut 1024 592+point 4 cut 1024 593)/2)
    have hp : middlePayment 592 = (648824820564:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 592+point 4 cut 1024 593)/2 = (16935481:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16935481:ℝ)/4218880) = (33971200:ℝ)/21312739 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16935481:ℝ)/4218880)-4 = (59961:ℝ)/4218880 by norm_num]
    exact paid_middle_592
  · change middlePayment 593 ≤ middleValue ((point 4 cut 1024 593+point 4 cut 1024 594)/2)
    have hp : middlePayment 593 = (648864604212:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 593+point 4 cut 1024 594)/2 = (84677911:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84677911:ℝ)/21094400) = (33971200:ℝ)/21312233 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84677911:ℝ)/21094400)-4 = (300311:ℝ)/21094400 by norm_num]
    exact paid_middle_593
  · change middlePayment 594 ≤ middleValue ((point 4 cut 1024 594+point 4 cut 1024 595)/2)
    have hp : middlePayment 594 = (648904389408:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 594+point 4 cut 1024 595)/2 = (84678417:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84678417:ℝ)/21094400) = (33971200:ℝ)/21311727 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84678417:ℝ)/21094400)-4 = (300817:ℝ)/21094400 by norm_num]
    exact paid_middle_594
  · change middlePayment 595 ≤ middleValue ((point 4 cut 1024 595+point 4 cut 1024 596)/2)
    have hp : middlePayment 595 = (648944176153:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 595+point 4 cut 1024 596)/2 = (84678923:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84678923:ℝ)/21094400) = (33971200:ℝ)/21311221 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84678923:ℝ)/21094400)-4 = (301323:ℝ)/21094400 by norm_num]
    exact paid_middle_595
  · change middlePayment 596 ≤ middleValue ((point 4 cut 1024 596+point 4 cut 1024 597)/2)
    have hp : middlePayment 596 = (648983964447:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 596+point 4 cut 1024 597)/2 = (84679429:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84679429:ℝ)/21094400) = (6794240:ℝ)/4262143 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84679429:ℝ)/21094400)-4 = (301829:ℝ)/21094400 by norm_num]
    exact paid_middle_596
  · change middlePayment 597 ≤ middleValue ((point 4 cut 1024 597+point 4 cut 1024 598)/2)
    have hp : middlePayment 597 = (649023754290:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 597+point 4 cut 1024 598)/2 = (16935987:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16935987:ℝ)/4218880) = (33971200:ℝ)/21310209 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16935987:ℝ)/4218880)-4 = (60467:ℝ)/4218880 by norm_num]
    exact paid_middle_597
  · change middlePayment 598 ≤ middleValue ((point 4 cut 1024 598+point 4 cut 1024 599)/2)
    have hp : middlePayment 598 = (649063545681:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 598+point 4 cut 1024 599)/2 = (84680441:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84680441:ℝ)/21094400) = (33971200:ℝ)/21309703 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84680441:ℝ)/21094400)-4 = (302841:ℝ)/21094400 by norm_num]
    exact paid_middle_598
  · change middlePayment 599 ≤ middleValue ((point 4 cut 1024 599+point 4 cut 1024 600)/2)
    have hp : middlePayment 599 = (649103338621:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 599+point 4 cut 1024 600)/2 = (84680947:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84680947:ℝ)/21094400) = (33971200:ℝ)/21309197 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84680947:ℝ)/21094400)-4 = (303347:ℝ)/21094400 by norm_num]
    exact paid_middle_599
  · change middlePayment 600 ≤ middleValue ((point 4 cut 1024 600+point 4 cut 1024 601)/2)
    have hp : middlePayment 600 = (649143133110:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 600+point 4 cut 1024 601)/2 = (84681453:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84681453:ℝ)/21094400) = (33971200:ℝ)/21308691 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84681453:ℝ)/21094400)-4 = (303853:ℝ)/21094400 by norm_num]
    exact paid_middle_600
  · change middlePayment 601 ≤ middleValue ((point 4 cut 1024 601+point 4 cut 1024 602)/2)
    have hp : middlePayment 601 = (649182929148:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 601+point 4 cut 1024 602)/2 = (84681959:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84681959:ℝ)/21094400) = (6794240:ℝ)/4261637 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84681959:ℝ)/21094400)-4 = (304359:ℝ)/21094400 by norm_num]
    exact paid_middle_601
  · change middlePayment 602 ≤ middleValue ((point 4 cut 1024 602+point 4 cut 1024 603)/2)
    have hp : middlePayment 602 = (649222726736:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 602+point 4 cut 1024 603)/2 = (16936493:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16936493:ℝ)/4218880) = (33971200:ℝ)/21307679 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16936493:ℝ)/4218880)-4 = (60973:ℝ)/4218880 by norm_num]
    exact paid_middle_602
  · change middlePayment 603 ≤ middleValue ((point 4 cut 1024 603+point 4 cut 1024 604)/2)
    have hp : middlePayment 603 = (649262525872:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 603+point 4 cut 1024 604)/2 = (84682971:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84682971:ℝ)/21094400) = (33971200:ℝ)/21307173 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84682971:ℝ)/21094400)-4 = (305371:ℝ)/21094400 by norm_num]
    exact paid_middle_603
  · change middlePayment 604 ≤ middleValue ((point 4 cut 1024 604+point 4 cut 1024 605)/2)
    have hp : middlePayment 604 = (649302326558:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 604+point 4 cut 1024 605)/2 = (84683477:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84683477:ℝ)/21094400) = (33971200:ℝ)/21306667 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84683477:ℝ)/21094400)-4 = (305877:ℝ)/21094400 by norm_num]
    exact paid_middle_604
  · change middlePayment 605 ≤ middleValue ((point 4 cut 1024 605+point 4 cut 1024 606)/2)
    have hp : middlePayment 605 = (649342128793:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 605+point 4 cut 1024 606)/2 = (84683983:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84683983:ℝ)/21094400) = (33971200:ℝ)/21306161 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84683983:ℝ)/21094400)-4 = (306383:ℝ)/21094400 by norm_num]
    exact paid_middle_605
  · change middlePayment 606 ≤ middleValue ((point 4 cut 1024 606+point 4 cut 1024 607)/2)
    have hp : middlePayment 606 = (649381932578:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 606+point 4 cut 1024 607)/2 = (84684489:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84684489:ℝ)/21094400) = (6794240:ℝ)/4261131 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84684489:ℝ)/21094400)-4 = (306889:ℝ)/21094400 by norm_num]
    exact paid_middle_606
  · change middlePayment 607 ≤ middleValue ((point 4 cut 1024 607+point 4 cut 1024 608)/2)
    have hp : middlePayment 607 = (649421737912:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 607+point 4 cut 1024 608)/2 = (16936999:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16936999:ℝ)/4218880) = (33971200:ℝ)/21305149 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16936999:ℝ)/4218880)-4 = (61479:ℝ)/4218880 by norm_num]
    exact paid_middle_607
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_037
