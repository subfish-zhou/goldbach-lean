import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints005
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_005 (j : Fin 16) : middlePayment (16*5+j.val) ≤
    middleValue ((point 4 cut 1024 (16*5+j.val)+point 4 cut 1024 (16*5+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 80 ≤ middleValue ((point 4 cut 1024 80+point 4 cut 1024 81)/2)
    have hp : middlePayment 80 = (628657208166:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 80+point 4 cut 1024 81)/2 = (84418333:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84418333:ℝ)/21094400) = (33971200:ℝ)/21571811 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84418333:ℝ)/21094400)-4 = (40733:ℝ)/21094400 by norm_num]
    exact paid_middle_80
  · change middlePayment 81 ≤ middleValue ((point 4 cut 1024 81+point 4 cut 1024 82)/2)
    have hp : middlePayment 81 = (628696209143:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 81+point 4 cut 1024 82)/2 = (84418839:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84418839:ℝ)/21094400) = (6794240:ℝ)/4314261 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84418839:ℝ)/21094400)-4 = (41239:ℝ)/21094400 by norm_num]
    exact paid_middle_81
  · change middlePayment 82 ≤ middleValue ((point 4 cut 1024 82+point 4 cut 1024 83)/2)
    have hp : middlePayment 82 = (628735211628:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 82+point 4 cut 1024 83)/2 = (16883869:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16883869:ℝ)/4218880) = (33971200:ℝ)/21570799 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16883869:ℝ)/4218880)-4 = (8349:ℝ)/4218880 by norm_num]
    exact paid_middle_82
  · change middlePayment 83 ≤ middleValue ((point 4 cut 1024 83+point 4 cut 1024 84)/2)
    have hp : middlePayment 83 = (628774215623:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 83+point 4 cut 1024 84)/2 = (84419851:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84419851:ℝ)/21094400) = (33971200:ℝ)/21570293 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84419851:ℝ)/21094400)-4 = (42251:ℝ)/21094400 by norm_num]
    exact paid_middle_83
  · change middlePayment 84 ≤ middleValue ((point 4 cut 1024 84+point 4 cut 1024 85)/2)
    have hp : middlePayment 84 = (628813221128:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 84+point 4 cut 1024 85)/2 = (84420357:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84420357:ℝ)/21094400) = (33971200:ℝ)/21569787 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84420357:ℝ)/21094400)-4 = (42757:ℝ)/21094400 by norm_num]
    exact paid_middle_84
  · change middlePayment 85 ≤ middleValue ((point 4 cut 1024 85+point 4 cut 1024 86)/2)
    have hp : middlePayment 85 = (628852228142:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 85+point 4 cut 1024 86)/2 = (84420863:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84420863:ℝ)/21094400) = (33971200:ℝ)/21569281 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84420863:ℝ)/21094400)-4 = (43263:ℝ)/21094400 by norm_num]
    exact paid_middle_85
  · change middlePayment 86 ≤ middleValue ((point 4 cut 1024 86+point 4 cut 1024 87)/2)
    have hp : middlePayment 86 = (628891236665:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 86+point 4 cut 1024 87)/2 = (84421369:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84421369:ℝ)/21094400) = (1358848:ℝ)/862751 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84421369:ℝ)/21094400)-4 = (43769:ℝ)/21094400 by norm_num]
    exact paid_middle_86
  · change middlePayment 87 ≤ middleValue ((point 4 cut 1024 87+point 4 cut 1024 88)/2)
    have hp : middlePayment 87 = (628930246697:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 87+point 4 cut 1024 88)/2 = (3376875:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3376875:ℝ)/843776) = (33971200:ℝ)/21568269 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3376875:ℝ)/843776)-4 = (1771:ℝ)/843776 by norm_num]
    exact paid_middle_87
  · change middlePayment 88 ≤ middleValue ((point 4 cut 1024 88+point 4 cut 1024 89)/2)
    have hp : middlePayment 88 = (628969258239:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 88+point 4 cut 1024 89)/2 = (84422381:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84422381:ℝ)/21094400) = (33971200:ℝ)/21567763 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84422381:ℝ)/21094400)-4 = (44781:ℝ)/21094400 by norm_num]
    exact paid_middle_88
  · change middlePayment 89 ≤ middleValue ((point 4 cut 1024 89+point 4 cut 1024 90)/2)
    have hp : middlePayment 89 = (629008271291:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 89+point 4 cut 1024 90)/2 = (84422887:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84422887:ℝ)/21094400) = (33971200:ℝ)/21567257 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84422887:ℝ)/21094400)-4 = (45287:ℝ)/21094400 by norm_num]
    exact paid_middle_89
  · change middlePayment 90 ≤ middleValue ((point 4 cut 1024 90+point 4 cut 1024 91)/2)
    have hp : middlePayment 90 = (629047285853:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 90+point 4 cut 1024 91)/2 = (84423393:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84423393:ℝ)/21094400) = (33971200:ℝ)/21566751 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84423393:ℝ)/21094400)-4 = (45793:ℝ)/21094400 by norm_num]
    exact paid_middle_90
  · change middlePayment 91 ≤ middleValue ((point 4 cut 1024 91+point 4 cut 1024 92)/2)
    have hp : middlePayment 91 = (629086301924:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 91+point 4 cut 1024 92)/2 = (84423899:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84423899:ℝ)/21094400) = (6794240:ℝ)/4313249 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84423899:ℝ)/21094400)-4 = (46299:ℝ)/21094400 by norm_num]
    exact paid_middle_91
  · change middlePayment 92 ≤ middleValue ((point 4 cut 1024 92+point 4 cut 1024 93)/2)
    have hp : middlePayment 92 = (629125319506:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 92+point 4 cut 1024 93)/2 = (16884881:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16884881:ℝ)/4218880) = (33971200:ℝ)/21565739 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16884881:ℝ)/4218880)-4 = (9361:ℝ)/4218880 by norm_num]
    exact paid_middle_92
  · change middlePayment 93 ≤ middleValue ((point 4 cut 1024 93+point 4 cut 1024 94)/2)
    have hp : middlePayment 93 = (629164338597:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 93+point 4 cut 1024 94)/2 = (84424911:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84424911:ℝ)/21094400) = (33971200:ℝ)/21565233 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84424911:ℝ)/21094400)-4 = (47311:ℝ)/21094400 by norm_num]
    exact paid_middle_93
  · change middlePayment 94 ≤ middleValue ((point 4 cut 1024 94+point 4 cut 1024 95)/2)
    have hp : middlePayment 94 = (629203359198:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 94+point 4 cut 1024 95)/2 = (84425417:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84425417:ℝ)/21094400) = (33971200:ℝ)/21564727 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84425417:ℝ)/21094400)-4 = (47817:ℝ)/21094400 by norm_num]
    exact paid_middle_94
  · change middlePayment 95 ≤ middleValue ((point 4 cut 1024 95+point 4 cut 1024 96)/2)
    have hp : middlePayment 95 = (629242381309:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 95+point 4 cut 1024 96)/2 = (84425923:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84425923:ℝ)/21094400) = (33971200:ℝ)/21564221 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84425923:ℝ)/21094400)-4 = (48323:ℝ)/21094400 by norm_num]
    exact paid_middle_95
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_005
