import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints013
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_013 (j : Fin 16) : middlePayment (16*13+j.val) ≤
    middleValue ((point 4 cut 1024 (16*13+j.val)+point 4 cut 1024 (16*13+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 208 ≤ middleValue ((point 4 cut 1024 208+point 4 cut 1024 209)/2)
    have hp : middlePayment 208 = (633661625197:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 208+point 4 cut 1024 209)/2 = (84483101:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84483101:ℝ)/21094400) = (33971200:ℝ)/21507043 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84483101:ℝ)/21094400)-4 = (105501:ℝ)/21094400 by norm_num]
    exact paid_middle_208
  · change middlePayment 209 ≤ middleValue ((point 4 cut 1024 209+point 4 cut 1024 210)/2)
    have hp : middlePayment 209 = (633700819957:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 209+point 4 cut 1024 210)/2 = (84483607:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84483607:ℝ)/21094400) = (33971200:ℝ)/21506537 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84483607:ℝ)/21094400)-4 = (106007:ℝ)/21094400 by norm_num]
    exact paid_middle_209
  · change middlePayment 210 ≤ middleValue ((point 4 cut 1024 210+point 4 cut 1024 211)/2)
    have hp : middlePayment 210 = (633740016236:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 210+point 4 cut 1024 211)/2 = (84484113:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84484113:ℝ)/21094400) = (33971200:ℝ)/21506031 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84484113:ℝ)/21094400)-4 = (106513:ℝ)/21094400 by norm_num]
    exact paid_middle_210
  · change middlePayment 211 ≤ middleValue ((point 4 cut 1024 211+point 4 cut 1024 212)/2)
    have hp : middlePayment 211 = (633779214034:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 211+point 4 cut 1024 212)/2 = (84484619:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84484619:ℝ)/21094400) = (1358848:ℝ)/860221 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84484619:ℝ)/21094400)-4 = (107019:ℝ)/21094400 by norm_num]
    exact paid_middle_211
  · change middlePayment 212 ≤ middleValue ((point 4 cut 1024 212+point 4 cut 1024 213)/2)
    have hp : middlePayment 212 = (633818413351:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 212+point 4 cut 1024 213)/2 = (3379405:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3379405:ℝ)/843776) = (33971200:ℝ)/21505019 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3379405:ℝ)/843776)-4 = (4301:ℝ)/843776 by norm_num]
    exact paid_middle_212
  · change middlePayment 213 ≤ middleValue ((point 4 cut 1024 213+point 4 cut 1024 214)/2)
    have hp : middlePayment 213 = (633857614188:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 213+point 4 cut 1024 214)/2 = (84485631:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84485631:ℝ)/21094400) = (33971200:ℝ)/21504513 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84485631:ℝ)/21094400)-4 = (108031:ℝ)/21094400 by norm_num]
    exact paid_middle_213
  · change middlePayment 214 ≤ middleValue ((point 4 cut 1024 214+point 4 cut 1024 215)/2)
    have hp : middlePayment 214 = (633896816543:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 214+point 4 cut 1024 215)/2 = (84486137:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84486137:ℝ)/21094400) = (33971200:ℝ)/21504007 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84486137:ℝ)/21094400)-4 = (108537:ℝ)/21094400 by norm_num]
    exact paid_middle_214
  · change middlePayment 215 ≤ middleValue ((point 4 cut 1024 215+point 4 cut 1024 216)/2)
    have hp : middlePayment 215 = (633936020417:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 215+point 4 cut 1024 216)/2 = (84486643:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84486643:ℝ)/21094400) = (33971200:ℝ)/21503501 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84486643:ℝ)/21094400)-4 = (109043:ℝ)/21094400 by norm_num]
    exact paid_middle_215
  · change middlePayment 216 ≤ middleValue ((point 4 cut 1024 216+point 4 cut 1024 217)/2)
    have hp : middlePayment 216 = (633975225811:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 216+point 4 cut 1024 217)/2 = (84487149:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84487149:ℝ)/21094400) = (6794240:ℝ)/4300599 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84487149:ℝ)/21094400)-4 = (109549:ℝ)/21094400 by norm_num]
    exact paid_middle_216
  · change middlePayment 217 ≤ middleValue ((point 4 cut 1024 217+point 4 cut 1024 218)/2)
    have hp : middlePayment 217 = (634014432724:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 217+point 4 cut 1024 218)/2 = (16897531:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16897531:ℝ)/4218880) = (33971200:ℝ)/21502489 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16897531:ℝ)/4218880)-4 = (22011:ℝ)/4218880 by norm_num]
    exact paid_middle_217
  · change middlePayment 218 ≤ middleValue ((point 4 cut 1024 218+point 4 cut 1024 219)/2)
    have hp : middlePayment 218 = (634053641157:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 218+point 4 cut 1024 219)/2 = (84488161:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84488161:ℝ)/21094400) = (33971200:ℝ)/21501983 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84488161:ℝ)/21094400)-4 = (110561:ℝ)/21094400 by norm_num]
    exact paid_middle_218
  · change middlePayment 219 ≤ middleValue ((point 4 cut 1024 219+point 4 cut 1024 220)/2)
    have hp : middlePayment 219 = (634092851109:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 219+point 4 cut 1024 220)/2 = (84488667:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84488667:ℝ)/21094400) = (33971200:ℝ)/21501477 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84488667:ℝ)/21094400)-4 = (111067:ℝ)/21094400 by norm_num]
    exact paid_middle_219
  · change middlePayment 220 ≤ middleValue ((point 4 cut 1024 220+point 4 cut 1024 221)/2)
    have hp : middlePayment 220 = (634132062581:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 220+point 4 cut 1024 221)/2 = (84489173:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84489173:ℝ)/21094400) = (33971200:ℝ)/21500971 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84489173:ℝ)/21094400)-4 = (111573:ℝ)/21094400 by norm_num]
    exact paid_middle_220
  · change middlePayment 221 ≤ middleValue ((point 4 cut 1024 221+point 4 cut 1024 222)/2)
    have hp : middlePayment 221 = (634171275572:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 221+point 4 cut 1024 222)/2 = (84489679:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84489679:ℝ)/21094400) = (6794240:ℝ)/4300093 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84489679:ℝ)/21094400)-4 = (112079:ℝ)/21094400 by norm_num]
    exact paid_middle_221
  · change middlePayment 222 ≤ middleValue ((point 4 cut 1024 222+point 4 cut 1024 223)/2)
    have hp : middlePayment 222 = (634210490083:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 222+point 4 cut 1024 223)/2 = (16898037:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16898037:ℝ)/4218880) = (33971200:ℝ)/21499959 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16898037:ℝ)/4218880)-4 = (22517:ℝ)/4218880 by norm_num]
    exact paid_middle_222
  · change middlePayment 223 ≤ middleValue ((point 4 cut 1024 223+point 4 cut 1024 224)/2)
    have hp : middlePayment 223 = (634249706114:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 223+point 4 cut 1024 224)/2 = (84490691:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84490691:ℝ)/21094400) = (33971200:ℝ)/21499453 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84490691:ℝ)/21094400)-4 = (113091:ℝ)/21094400 by norm_num]
    exact paid_middle_223
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_013
