import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints063
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_063 (j : Fin 16) : middlePayment (16*63+j.val) ≤
    middleValue ((point 4 cut 1024 (16*63+j.val)+point 4 cut 1024 (16*63+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 1008 ≤ middleValue ((point 4 cut 1024 1008+point 4 cut 1024 1009)/2)
    have hp : middlePayment 1008 = (665509425730:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1008+point 4 cut 1024 1009)/2 = (84887901:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84887901:ℝ)/21094400) = (33971200:ℝ)/21102243 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84887901:ℝ)/21094400)-4 = (510301:ℝ)/21094400 by norm_num]
    exact paid_middle_1008
  · change middlePayment 1009 ≤ middleValue ((point 4 cut 1024 1009+point 4 cut 1024 1010)/2)
    have hp : middlePayment 1009 = (665549860390:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1009+point 4 cut 1024 1010)/2 = (84888407:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84888407:ℝ)/21094400) = (33971200:ℝ)/21101737 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84888407:ℝ)/21094400)-4 = (510807:ℝ)/21094400 by norm_num]
    exact paid_middle_1009
  · change middlePayment 1010 ≤ middleValue ((point 4 cut 1024 1010+point 4 cut 1024 1011)/2)
    have hp : middlePayment 1010 = (665590296631:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1010+point 4 cut 1024 1011)/2 = (84888913:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84888913:ℝ)/21094400) = (33971200:ℝ)/21101231 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84888913:ℝ)/21094400)-4 = (511313:ℝ)/21094400 by norm_num]
    exact paid_middle_1010
  · change middlePayment 1011 ≤ middleValue ((point 4 cut 1024 1011+point 4 cut 1024 1012)/2)
    have hp : middlePayment 1011 = (665630734454:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1011+point 4 cut 1024 1012)/2 = (84889419:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84889419:ℝ)/21094400) = (1358848:ℝ)/844029 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84889419:ℝ)/21094400)-4 = (511819:ℝ)/21094400 by norm_num]
    exact paid_middle_1011
  · change middlePayment 1012 ≤ middleValue ((point 4 cut 1024 1012+point 4 cut 1024 1013)/2)
    have hp : middlePayment 1012 = (665671173859:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1012+point 4 cut 1024 1013)/2 = (3395597:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3395597:ℝ)/843776) = (33971200:ℝ)/21100219 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3395597:ℝ)/843776)-4 = (20493:ℝ)/843776 by norm_num]
    exact paid_middle_1012
  · change middlePayment 1013 ≤ middleValue ((point 4 cut 1024 1013+point 4 cut 1024 1014)/2)
    have hp : middlePayment 1013 = (665711614846:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1013+point 4 cut 1024 1014)/2 = (84890431:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84890431:ℝ)/21094400) = (33971200:ℝ)/21099713 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84890431:ℝ)/21094400)-4 = (512831:ℝ)/21094400 by norm_num]
    exact paid_middle_1013
  · change middlePayment 1014 ≤ middleValue ((point 4 cut 1024 1014+point 4 cut 1024 1015)/2)
    have hp : middlePayment 1014 = (665752057415:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1014+point 4 cut 1024 1015)/2 = (84890937:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84890937:ℝ)/21094400) = (33971200:ℝ)/21099207 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84890937:ℝ)/21094400)-4 = (513337:ℝ)/21094400 by norm_num]
    exact paid_middle_1014
  · change middlePayment 1015 ≤ middleValue ((point 4 cut 1024 1015+point 4 cut 1024 1016)/2)
    have hp : middlePayment 1015 = (665792501566:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1015+point 4 cut 1024 1016)/2 = (84891443:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84891443:ℝ)/21094400) = (33971200:ℝ)/21098701 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84891443:ℝ)/21094400)-4 = (513843:ℝ)/21094400 by norm_num]
    exact paid_middle_1015
  · change middlePayment 1016 ≤ middleValue ((point 4 cut 1024 1016+point 4 cut 1024 1017)/2)
    have hp : middlePayment 1016 = (665832947299:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1016+point 4 cut 1024 1017)/2 = (84891949:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84891949:ℝ)/21094400) = (6794240:ℝ)/4219639 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84891949:ℝ)/21094400)-4 = (514349:ℝ)/21094400 by norm_num]
    exact paid_middle_1016
  · change middlePayment 1017 ≤ middleValue ((point 4 cut 1024 1017+point 4 cut 1024 1018)/2)
    have hp : middlePayment 1017 = (665873394614:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1017+point 4 cut 1024 1018)/2 = (16978491:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16978491:ℝ)/4218880) = (33971200:ℝ)/21097689 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16978491:ℝ)/4218880)-4 = (102971:ℝ)/4218880 by norm_num]
    exact paid_middle_1017
  · change middlePayment 1018 ≤ middleValue ((point 4 cut 1024 1018+point 4 cut 1024 1019)/2)
    have hp : middlePayment 1018 = (665913843511:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1018+point 4 cut 1024 1019)/2 = (84892961:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84892961:ℝ)/21094400) = (33971200:ℝ)/21097183 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84892961:ℝ)/21094400)-4 = (515361:ℝ)/21094400 by norm_num]
    exact paid_middle_1018
  · change middlePayment 1019 ≤ middleValue ((point 4 cut 1024 1019+point 4 cut 1024 1020)/2)
    have hp : middlePayment 1019 = (665954293990:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1019+point 4 cut 1024 1020)/2 = (84893467:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84893467:ℝ)/21094400) = (33971200:ℝ)/21096677 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84893467:ℝ)/21094400)-4 = (515867:ℝ)/21094400 by norm_num]
    exact paid_middle_1019
  · change middlePayment 1020 ≤ middleValue ((point 4 cut 1024 1020+point 4 cut 1024 1021)/2)
    have hp : middlePayment 1020 = (665994746052:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1020+point 4 cut 1024 1021)/2 = (84893973:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84893973:ℝ)/21094400) = (33971200:ℝ)/21096171 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84893973:ℝ)/21094400)-4 = (516373:ℝ)/21094400 by norm_num]
    exact paid_middle_1020
  · change middlePayment 1021 ≤ middleValue ((point 4 cut 1024 1021+point 4 cut 1024 1022)/2)
    have hp : middlePayment 1021 = (666035199697:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1021+point 4 cut 1024 1022)/2 = (84894479:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84894479:ℝ)/21094400) = (6794240:ℝ)/4219133 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84894479:ℝ)/21094400)-4 = (516879:ℝ)/21094400 by norm_num]
    exact paid_middle_1021
  · change middlePayment 1022 ≤ middleValue ((point 4 cut 1024 1022+point 4 cut 1024 1023)/2)
    have hp : middlePayment 1022 = (666075654924:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1022+point 4 cut 1024 1023)/2 = (16978997:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16978997:ℝ)/4218880) = (33971200:ℝ)/21095159 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16978997:ℝ)/4218880)-4 = (103477:ℝ)/4218880 by norm_num]
    exact paid_middle_1022
  · change middlePayment 1023 ≤ middleValue ((point 4 cut 1024 1023+point 4 cut 1024 1024)/2)
    have hp : middlePayment 1023 = (666116111734:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1023+point 4 cut 1024 1024)/2 = (84895491:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84895491:ℝ)/21094400) = (33971200:ℝ)/21094653 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84895491:ℝ)/21094400)-4 = (517891:ℝ)/21094400 by norm_num]
    exact paid_middle_1023
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_063
