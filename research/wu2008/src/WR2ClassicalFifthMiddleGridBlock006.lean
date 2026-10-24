import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints006
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_006 (j : Fin 16) : middlePayment (16*6+j.val) ≤
    middleValue ((point 4 cut 1024 (16*6+j.val)+point 4 cut 1024 (16*6+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 96 ≤ middleValue ((point 4 cut 1024 96+point 4 cut 1024 97)/2)
    have hp : middlePayment 96 = (629281404931:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 96+point 4 cut 1024 97)/2 = (84426429:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84426429:ℝ)/21094400) = (6794240:ℝ)/4312743 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84426429:ℝ)/21094400)-4 = (48829:ℝ)/21094400 by norm_num]
    exact paid_middle_96
  · change middlePayment 97 ≤ middleValue ((point 4 cut 1024 97+point 4 cut 1024 98)/2)
    have hp : middlePayment 97 = (629320430063:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 97+point 4 cut 1024 98)/2 = (16885387:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16885387:ℝ)/4218880) = (33971200:ℝ)/21563209 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16885387:ℝ)/4218880)-4 = (9867:ℝ)/4218880 by norm_num]
    exact paid_middle_97
  · change middlePayment 98 ≤ middleValue ((point 4 cut 1024 98+point 4 cut 1024 99)/2)
    have hp : middlePayment 98 = (629359456705:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 98+point 4 cut 1024 99)/2 = (84427441:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84427441:ℝ)/21094400) = (33971200:ℝ)/21562703 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84427441:ℝ)/21094400)-4 = (49841:ℝ)/21094400 by norm_num]
    exact paid_middle_98
  · change middlePayment 99 ≤ middleValue ((point 4 cut 1024 99+point 4 cut 1024 100)/2)
    have hp : middlePayment 99 = (629398484858:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 99+point 4 cut 1024 100)/2 = (84427947:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84427947:ℝ)/21094400) = (33971200:ℝ)/21562197 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84427947:ℝ)/21094400)-4 = (50347:ℝ)/21094400 by norm_num]
    exact paid_middle_99
  · change middlePayment 100 ≤ middleValue ((point 4 cut 1024 100+point 4 cut 1024 101)/2)
    have hp : middlePayment 100 = (629437514521:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 100+point 4 cut 1024 101)/2 = (84428453:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84428453:ℝ)/21094400) = (33971200:ℝ)/21561691 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84428453:ℝ)/21094400)-4 = (50853:ℝ)/21094400 by norm_num]
    exact paid_middle_100
  · change middlePayment 101 ≤ middleValue ((point 4 cut 1024 101+point 4 cut 1024 102)/2)
    have hp : middlePayment 101 = (629476545694:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 101+point 4 cut 1024 102)/2 = (84428959:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84428959:ℝ)/21094400) = (6794240:ℝ)/4312237 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84428959:ℝ)/21094400)-4 = (51359:ℝ)/21094400 by norm_num]
    exact paid_middle_101
  · change middlePayment 102 ≤ middleValue ((point 4 cut 1024 102+point 4 cut 1024 103)/2)
    have hp : middlePayment 102 = (629515578378:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 102+point 4 cut 1024 103)/2 = (16885893:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16885893:ℝ)/4218880) = (33971200:ℝ)/21560679 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16885893:ℝ)/4218880)-4 = (10373:ℝ)/4218880 by norm_num]
    exact paid_middle_102
  · change middlePayment 103 ≤ middleValue ((point 4 cut 1024 103+point 4 cut 1024 104)/2)
    have hp : middlePayment 103 = (629554612573:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 103+point 4 cut 1024 104)/2 = (84429971:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84429971:ℝ)/21094400) = (33971200:ℝ)/21560173 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84429971:ℝ)/21094400)-4 = (52371:ℝ)/21094400 by norm_num]
    exact paid_middle_103
  · change middlePayment 104 ≤ middleValue ((point 4 cut 1024 104+point 4 cut 1024 105)/2)
    have hp : middlePayment 104 = (629593648279:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 104+point 4 cut 1024 105)/2 = (84430477:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84430477:ℝ)/21094400) = (33971200:ℝ)/21559667 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84430477:ℝ)/21094400)-4 = (52877:ℝ)/21094400 by norm_num]
    exact paid_middle_104
  · change middlePayment 105 ≤ middleValue ((point 4 cut 1024 105+point 4 cut 1024 106)/2)
    have hp : middlePayment 105 = (629632685496:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 105+point 4 cut 1024 106)/2 = (84430983:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84430983:ℝ)/21094400) = (33971200:ℝ)/21559161 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84430983:ℝ)/21094400)-4 = (53383:ℝ)/21094400 by norm_num]
    exact paid_middle_105
  · change middlePayment 106 ≤ middleValue ((point 4 cut 1024 106+point 4 cut 1024 107)/2)
    have hp : middlePayment 106 = (629671724223:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 106+point 4 cut 1024 107)/2 = (84431489:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84431489:ℝ)/21094400) = (6794240:ℝ)/4311731 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84431489:ℝ)/21094400)-4 = (53889:ℝ)/21094400 by norm_num]
    exact paid_middle_106
  · change middlePayment 107 ≤ middleValue ((point 4 cut 1024 107+point 4 cut 1024 108)/2)
    have hp : middlePayment 107 = (629710764462:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 107+point 4 cut 1024 108)/2 = (16886399:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16886399:ℝ)/4218880) = (33971200:ℝ)/21558149 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16886399:ℝ)/4218880)-4 = (10879:ℝ)/4218880 by norm_num]
    exact paid_middle_107
  · change middlePayment 108 ≤ middleValue ((point 4 cut 1024 108+point 4 cut 1024 109)/2)
    have hp : middlePayment 108 = (629749806212:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 108+point 4 cut 1024 109)/2 = (84432501:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84432501:ℝ)/21094400) = (33971200:ℝ)/21557643 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84432501:ℝ)/21094400)-4 = (54901:ℝ)/21094400 by norm_num]
    exact paid_middle_108
  · change middlePayment 109 ≤ middleValue ((point 4 cut 1024 109+point 4 cut 1024 110)/2)
    have hp : middlePayment 109 = (629788849472:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 109+point 4 cut 1024 110)/2 = (84433007:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84433007:ℝ)/21094400) = (33971200:ℝ)/21557137 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84433007:ℝ)/21094400)-4 = (55407:ℝ)/21094400 by norm_num]
    exact paid_middle_109
  · change middlePayment 110 ≤ middleValue ((point 4 cut 1024 110+point 4 cut 1024 111)/2)
    have hp : middlePayment 110 = (629827894244:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 110+point 4 cut 1024 111)/2 = (84433513:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84433513:ℝ)/21094400) = (33971200:ℝ)/21556631 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84433513:ℝ)/21094400)-4 = (55913:ℝ)/21094400 by norm_num]
    exact paid_middle_110
  · change middlePayment 111 ≤ middleValue ((point 4 cut 1024 111+point 4 cut 1024 112)/2)
    have hp : middlePayment 111 = (629866940528:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 111+point 4 cut 1024 112)/2 = (84434019:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84434019:ℝ)/21094400) = (1358848:ℝ)/862245 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84434019:ℝ)/21094400)-4 = (56419:ℝ)/21094400 by norm_num]
    exact paid_middle_111
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_006
