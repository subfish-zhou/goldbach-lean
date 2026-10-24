import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints015
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_015 (j : Fin 16) : middlePayment (16*15+j.val) ≤
    middleValue ((point 4 cut 1024 (16*15+j.val)+point 4 cut 1024 (16*15+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 240 ≤ middleValue ((point 4 cut 1024 240+point 4 cut 1024 241)/2)
    have hp : middlePayment 240 = (634916611248:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 240+point 4 cut 1024 241)/2 = (84499293:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84499293:ℝ)/21094400) = (33971200:ℝ)/21490851 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84499293:ℝ)/21094400)-4 = (121693:ℝ)/21094400 by norm_num]
    exact paid_middle_240
  · change middlePayment 241 ≤ middleValue ((point 4 cut 1024 241+point 4 cut 1024 242)/2)
    have hp : middlePayment 241 = (634955854649:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 241+point 4 cut 1024 242)/2 = (84499799:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84499799:ℝ)/21094400) = (6794240:ℝ)/4298069 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84499799:ℝ)/21094400)-4 = (122199:ℝ)/21094400 by norm_num]
    exact paid_middle_241
  · change middlePayment 242 ≤ middleValue ((point 4 cut 1024 242+point 4 cut 1024 243)/2)
    have hp : middlePayment 242 = (634995099571:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 242+point 4 cut 1024 243)/2 = (16900061:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16900061:ℝ)/4218880) = (33971200:ℝ)/21489839 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16900061:ℝ)/4218880)-4 = (24541:ℝ)/4218880 by norm_num]
    exact paid_middle_242
  · change middlePayment 243 ≤ middleValue ((point 4 cut 1024 243+point 4 cut 1024 244)/2)
    have hp : middlePayment 243 = (635034346015:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 243+point 4 cut 1024 244)/2 = (84500811:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84500811:ℝ)/21094400) = (33971200:ℝ)/21489333 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84500811:ℝ)/21094400)-4 = (123211:ℝ)/21094400 by norm_num]
    exact paid_middle_243
  · change middlePayment 244 ≤ middleValue ((point 4 cut 1024 244+point 4 cut 1024 245)/2)
    have hp : middlePayment 244 = (635073593979:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 244+point 4 cut 1024 245)/2 = (84501317:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84501317:ℝ)/21094400) = (33971200:ℝ)/21488827 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84501317:ℝ)/21094400)-4 = (123717:ℝ)/21094400 by norm_num]
    exact paid_middle_244
  · change middlePayment 245 ≤ middleValue ((point 4 cut 1024 245+point 4 cut 1024 246)/2)
    have hp : middlePayment 245 = (635112843466:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 245+point 4 cut 1024 246)/2 = (84501823:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84501823:ℝ)/21094400) = (33971200:ℝ)/21488321 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84501823:ℝ)/21094400)-4 = (124223:ℝ)/21094400 by norm_num]
    exact paid_middle_245
  · change middlePayment 246 ≤ middleValue ((point 4 cut 1024 246+point 4 cut 1024 247)/2)
    have hp : middlePayment 246 = (635152094474:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 246+point 4 cut 1024 247)/2 = (84502329:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84502329:ℝ)/21094400) = (6794240:ℝ)/4297563 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84502329:ℝ)/21094400)-4 = (124729:ℝ)/21094400 by norm_num]
    exact paid_middle_246
  · change middlePayment 247 ≤ middleValue ((point 4 cut 1024 247+point 4 cut 1024 248)/2)
    have hp : middlePayment 247 = (635191347004:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 247+point 4 cut 1024 248)/2 = (16900567:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16900567:ℝ)/4218880) = (33971200:ℝ)/21487309 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16900567:ℝ)/4218880)-4 = (25047:ℝ)/4218880 by norm_num]
    exact paid_middle_247
  · change middlePayment 248 ≤ middleValue ((point 4 cut 1024 248+point 4 cut 1024 249)/2)
    have hp : middlePayment 248 = (635230601055:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 248+point 4 cut 1024 249)/2 = (84503341:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84503341:ℝ)/21094400) = (33971200:ℝ)/21486803 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84503341:ℝ)/21094400)-4 = (125741:ℝ)/21094400 by norm_num]
    exact paid_middle_248
  · change middlePayment 249 ≤ middleValue ((point 4 cut 1024 249+point 4 cut 1024 250)/2)
    have hp : middlePayment 249 = (635269856628:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 249+point 4 cut 1024 250)/2 = (84503847:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84503847:ℝ)/21094400) = (33971200:ℝ)/21486297 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84503847:ℝ)/21094400)-4 = (126247:ℝ)/21094400 by norm_num]
    exact paid_middle_249
  · change middlePayment 250 ≤ middleValue ((point 4 cut 1024 250+point 4 cut 1024 251)/2)
    have hp : middlePayment 250 = (635309113723:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 250+point 4 cut 1024 251)/2 = (84504353:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84504353:ℝ)/21094400) = (33971200:ℝ)/21485791 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84504353:ℝ)/21094400)-4 = (126753:ℝ)/21094400 by norm_num]
    exact paid_middle_250
  · change middlePayment 251 ≤ middleValue ((point 4 cut 1024 251+point 4 cut 1024 252)/2)
    have hp : middlePayment 251 = (635348372340:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 251+point 4 cut 1024 252)/2 = (84504859:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84504859:ℝ)/21094400) = (6794240:ℝ)/4297057 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84504859:ℝ)/21094400)-4 = (127259:ℝ)/21094400 by norm_num]
    exact paid_middle_251
  · change middlePayment 252 ≤ middleValue ((point 4 cut 1024 252+point 4 cut 1024 253)/2)
    have hp : middlePayment 252 = (635387632479:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 252+point 4 cut 1024 253)/2 = (16901073:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16901073:ℝ)/4218880) = (33971200:ℝ)/21484779 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16901073:ℝ)/4218880)-4 = (25553:ℝ)/4218880 by norm_num]
    exact paid_middle_252
  · change middlePayment 253 ≤ middleValue ((point 4 cut 1024 253+point 4 cut 1024 254)/2)
    have hp : middlePayment 253 = (635426894141:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 253+point 4 cut 1024 254)/2 = (84505871:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84505871:ℝ)/21094400) = (33971200:ℝ)/21484273 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84505871:ℝ)/21094400)-4 = (128271:ℝ)/21094400 by norm_num]
    exact paid_middle_253
  · change middlePayment 254 ≤ middleValue ((point 4 cut 1024 254+point 4 cut 1024 255)/2)
    have hp : middlePayment 254 = (635466157324:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 254+point 4 cut 1024 255)/2 = (84506377:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84506377:ℝ)/21094400) = (33971200:ℝ)/21483767 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84506377:ℝ)/21094400)-4 = (128777:ℝ)/21094400 by norm_num]
    exact paid_middle_254
  · change middlePayment 255 ≤ middleValue ((point 4 cut 1024 255+point 4 cut 1024 256)/2)
    have hp : middlePayment 255 = (635505422030:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 255+point 4 cut 1024 256)/2 = (84506883:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84506883:ℝ)/21094400) = (33971200:ℝ)/21483261 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84506883:ℝ)/21094400)-4 = (129283:ℝ)/21094400 by norm_num]
    exact paid_middle_255
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_015
