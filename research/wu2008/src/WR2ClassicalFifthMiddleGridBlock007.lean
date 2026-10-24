import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints007
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_007 (j : Fin 16) : middlePayment (16*7+j.val) ≤
    middleValue ((point 4 cut 1024 (16*7+j.val)+point 4 cut 1024 (16*7+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 112 ≤ middleValue ((point 4 cut 1024 112+point 4 cut 1024 113)/2)
    have hp : middlePayment 112 = (629905988323:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 112+point 4 cut 1024 113)/2 = (3377381:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3377381:ℝ)/843776) = (33971200:ℝ)/21555619 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3377381:ℝ)/843776)-4 = (2277:ℝ)/843776 by norm_num]
    exact paid_middle_112
  · change middlePayment 113 ≤ middleValue ((point 4 cut 1024 113+point 4 cut 1024 114)/2)
    have hp : middlePayment 113 = (629945037629:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 113+point 4 cut 1024 114)/2 = (84435031:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84435031:ℝ)/21094400) = (33971200:ℝ)/21555113 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84435031:ℝ)/21094400)-4 = (57431:ℝ)/21094400 by norm_num]
    exact paid_middle_113
  · change middlePayment 114 ≤ middleValue ((point 4 cut 1024 114+point 4 cut 1024 115)/2)
    have hp : middlePayment 114 = (629984088447:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 114+point 4 cut 1024 115)/2 = (84435537:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84435537:ℝ)/21094400) = (33971200:ℝ)/21554607 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84435537:ℝ)/21094400)-4 = (57937:ℝ)/21094400 by norm_num]
    exact paid_middle_114
  · change middlePayment 115 ≤ middleValue ((point 4 cut 1024 115+point 4 cut 1024 116)/2)
    have hp : middlePayment 115 = (630023140776:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 115+point 4 cut 1024 116)/2 = (84436043:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84436043:ℝ)/21094400) = (33971200:ℝ)/21554101 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84436043:ℝ)/21094400)-4 = (58443:ℝ)/21094400 by norm_num]
    exact paid_middle_115
  · change middlePayment 116 ≤ middleValue ((point 4 cut 1024 116+point 4 cut 1024 117)/2)
    have hp : middlePayment 116 = (630062194617:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 116+point 4 cut 1024 117)/2 = (84436549:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84436549:ℝ)/21094400) = (6794240:ℝ)/4310719 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84436549:ℝ)/21094400)-4 = (58949:ℝ)/21094400 by norm_num]
    exact paid_middle_116
  · change middlePayment 117 ≤ middleValue ((point 4 cut 1024 117+point 4 cut 1024 118)/2)
    have hp : middlePayment 117 = (630101249970:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 117+point 4 cut 1024 118)/2 = (16887411:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16887411:ℝ)/4218880) = (33971200:ℝ)/21553089 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16887411:ℝ)/4218880)-4 = (11891:ℝ)/4218880 by norm_num]
    exact paid_middle_117
  · change middlePayment 118 ≤ middleValue ((point 4 cut 1024 118+point 4 cut 1024 119)/2)
    have hp : middlePayment 118 = (630140306835:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 118+point 4 cut 1024 119)/2 = (84437561:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84437561:ℝ)/21094400) = (33971200:ℝ)/21552583 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84437561:ℝ)/21094400)-4 = (59961:ℝ)/21094400 by norm_num]
    exact paid_middle_118
  · change middlePayment 119 ≤ middleValue ((point 4 cut 1024 119+point 4 cut 1024 120)/2)
    have hp : middlePayment 119 = (630179365211:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 119+point 4 cut 1024 120)/2 = (84438067:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84438067:ℝ)/21094400) = (33971200:ℝ)/21552077 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84438067:ℝ)/21094400)-4 = (60467:ℝ)/21094400 by norm_num]
    exact paid_middle_119
  · change middlePayment 120 ≤ middleValue ((point 4 cut 1024 120+point 4 cut 1024 121)/2)
    have hp : middlePayment 120 = (630218425100:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 120+point 4 cut 1024 121)/2 = (84438573:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84438573:ℝ)/21094400) = (33971200:ℝ)/21551571 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84438573:ℝ)/21094400)-4 = (60973:ℝ)/21094400 by norm_num]
    exact paid_middle_120
  · change middlePayment 121 ≤ middleValue ((point 4 cut 1024 121+point 4 cut 1024 122)/2)
    have hp : middlePayment 121 = (630257486501:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 121+point 4 cut 1024 122)/2 = (84439079:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84439079:ℝ)/21094400) = (6794240:ℝ)/4310213 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84439079:ℝ)/21094400)-4 = (61479:ℝ)/21094400 by norm_num]
    exact paid_middle_121
  · change middlePayment 122 ≤ middleValue ((point 4 cut 1024 122+point 4 cut 1024 123)/2)
    have hp : middlePayment 122 = (630296549414:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 122+point 4 cut 1024 123)/2 = (16887917:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16887917:ℝ)/4218880) = (33971200:ℝ)/21550559 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16887917:ℝ)/4218880)-4 = (12397:ℝ)/4218880 by norm_num]
    exact paid_middle_122
  · change middlePayment 123 ≤ middleValue ((point 4 cut 1024 123+point 4 cut 1024 124)/2)
    have hp : middlePayment 123 = (630335613839:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 123+point 4 cut 1024 124)/2 = (84440091:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84440091:ℝ)/21094400) = (33971200:ℝ)/21550053 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84440091:ℝ)/21094400)-4 = (62491:ℝ)/21094400 by norm_num]
    exact paid_middle_123
  · change middlePayment 124 ≤ middleValue ((point 4 cut 1024 124+point 4 cut 1024 125)/2)
    have hp : middlePayment 124 = (630374679776:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 124+point 4 cut 1024 125)/2 = (84440597:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84440597:ℝ)/21094400) = (33971200:ℝ)/21549547 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84440597:ℝ)/21094400)-4 = (62997:ℝ)/21094400 by norm_num]
    exact paid_middle_124
  · change middlePayment 125 ≤ middleValue ((point 4 cut 1024 125+point 4 cut 1024 126)/2)
    have hp : middlePayment 125 = (630413747226:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 125+point 4 cut 1024 126)/2 = (84441103:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84441103:ℝ)/21094400) = (33971200:ℝ)/21549041 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84441103:ℝ)/21094400)-4 = (63503:ℝ)/21094400 by norm_num]
    exact paid_middle_125
  · change middlePayment 126 ≤ middleValue ((point 4 cut 1024 126+point 4 cut 1024 127)/2)
    have hp : middlePayment 126 = (630452816188:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 126+point 4 cut 1024 127)/2 = (84441609:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84441609:ℝ)/21094400) = (6794240:ℝ)/4309707 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84441609:ℝ)/21094400)-4 = (64009:ℝ)/21094400 by norm_num]
    exact paid_middle_126
  · change middlePayment 127 ≤ middleValue ((point 4 cut 1024 127+point 4 cut 1024 128)/2)
    have hp : middlePayment 127 = (630491886663:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 127+point 4 cut 1024 128)/2 = (16888423:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16888423:ℝ)/4218880) = (33971200:ℝ)/21548029 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16888423:ℝ)/4218880)-4 = (12903:ℝ)/4218880 by norm_num]
    exact paid_middle_127
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_007
