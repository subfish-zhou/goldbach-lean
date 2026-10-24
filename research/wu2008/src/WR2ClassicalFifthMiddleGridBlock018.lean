import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints018
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_018 (j : Fin 16) : middlePayment (16*18+j.val) ≤
    middleValue ((point 4 cut 1024 (16*18+j.val)+point 4 cut 1024 (16*18+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 288 ≤ middleValue ((point 4 cut 1024 288+point 4 cut 1024 289)/2)
    have hp : middlePayment 288 = (636802011809:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 288+point 4 cut 1024 289)/2 = (84523581:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84523581:ℝ)/21094400) = (33971200:ℝ)/21466563 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84523581:ℝ)/21094400)-4 = (145981:ℝ)/21094400 by norm_num]
    exact paid_middle_288
  · change middlePayment 289 ≤ middleValue ((point 4 cut 1024 289+point 4 cut 1024 290)/2)
    have hp : middlePayment 289 = (636841328318:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 289+point 4 cut 1024 290)/2 = (84524087:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84524087:ℝ)/21094400) = (33971200:ℝ)/21466057 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84524087:ℝ)/21094400)-4 = (146487:ℝ)/21094400 by norm_num]
    exact paid_middle_289
  · change middlePayment 290 ≤ middleValue ((point 4 cut 1024 290+point 4 cut 1024 291)/2)
    have hp : middlePayment 290 = (636880646351:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 290+point 4 cut 1024 291)/2 = (84524593:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84524593:ℝ)/21094400) = (33971200:ℝ)/21465551 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84524593:ℝ)/21094400)-4 = (146993:ℝ)/21094400 by norm_num]
    exact paid_middle_290
  · change middlePayment 291 ≤ middleValue ((point 4 cut 1024 291+point 4 cut 1024 292)/2)
    have hp : middlePayment 291 = (636919965909:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 291+point 4 cut 1024 292)/2 = (84525099:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84525099:ℝ)/21094400) = (6794240:ℝ)/4293009 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84525099:ℝ)/21094400)-4 = (147499:ℝ)/21094400 by norm_num]
    exact paid_middle_291
  · change middlePayment 292 ≤ middleValue ((point 4 cut 1024 292+point 4 cut 1024 293)/2)
    have hp : middlePayment 292 = (636959286993:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 292+point 4 cut 1024 293)/2 = (16905121:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16905121:ℝ)/4218880) = (33971200:ℝ)/21464539 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16905121:ℝ)/4218880)-4 = (29601:ℝ)/4218880 by norm_num]
    exact paid_middle_292
  · change middlePayment 293 ≤ middleValue ((point 4 cut 1024 293+point 4 cut 1024 294)/2)
    have hp : middlePayment 293 = (636998609601:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 293+point 4 cut 1024 294)/2 = (84526111:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84526111:ℝ)/21094400) = (33971200:ℝ)/21464033 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84526111:ℝ)/21094400)-4 = (148511:ℝ)/21094400 by norm_num]
    exact paid_middle_293
  · change middlePayment 294 ≤ middleValue ((point 4 cut 1024 294+point 4 cut 1024 295)/2)
    have hp : middlePayment 294 = (637037933735:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 294+point 4 cut 1024 295)/2 = (84526617:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84526617:ℝ)/21094400) = (33971200:ℝ)/21463527 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84526617:ℝ)/21094400)-4 = (149017:ℝ)/21094400 by norm_num]
    exact paid_middle_294
  · change middlePayment 295 ≤ middleValue ((point 4 cut 1024 295+point 4 cut 1024 296)/2)
    have hp : middlePayment 295 = (637077259394:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 295+point 4 cut 1024 296)/2 = (84527123:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84527123:ℝ)/21094400) = (33971200:ℝ)/21463021 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84527123:ℝ)/21094400)-4 = (149523:ℝ)/21094400 by norm_num]
    exact paid_middle_295
  · change middlePayment 296 ≤ middleValue ((point 4 cut 1024 296+point 4 cut 1024 297)/2)
    have hp : middlePayment 296 = (637116586579:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 296+point 4 cut 1024 297)/2 = (84527629:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84527629:ℝ)/21094400) = (6794240:ℝ)/4292503 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84527629:ℝ)/21094400)-4 = (150029:ℝ)/21094400 by norm_num]
    exact paid_middle_296
  · change middlePayment 297 ≤ middleValue ((point 4 cut 1024 297+point 4 cut 1024 298)/2)
    have hp : middlePayment 297 = (637155915289:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 297+point 4 cut 1024 298)/2 = (16905627:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16905627:ℝ)/4218880) = (33971200:ℝ)/21462009 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16905627:ℝ)/4218880)-4 = (30107:ℝ)/4218880 by norm_num]
    exact paid_middle_297
  · change middlePayment 298 ≤ middleValue ((point 4 cut 1024 298+point 4 cut 1024 299)/2)
    have hp : middlePayment 298 = (637195245524:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 298+point 4 cut 1024 299)/2 = (84528641:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84528641:ℝ)/21094400) = (33971200:ℝ)/21461503 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84528641:ℝ)/21094400)-4 = (151041:ℝ)/21094400 by norm_num]
    exact paid_middle_298
  · change middlePayment 299 ≤ middleValue ((point 4 cut 1024 299+point 4 cut 1024 300)/2)
    have hp : middlePayment 299 = (637234577285:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 299+point 4 cut 1024 300)/2 = (84529147:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84529147:ℝ)/21094400) = (33971200:ℝ)/21460997 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84529147:ℝ)/21094400)-4 = (151547:ℝ)/21094400 by norm_num]
    exact paid_middle_299
  · change middlePayment 300 ≤ middleValue ((point 4 cut 1024 300+point 4 cut 1024 301)/2)
    have hp : middlePayment 300 = (637273910572:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 300+point 4 cut 1024 301)/2 = (84529653:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84529653:ℝ)/21094400) = (33971200:ℝ)/21460491 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84529653:ℝ)/21094400)-4 = (152053:ℝ)/21094400 by norm_num]
    exact paid_middle_300
  · change middlePayment 301 ≤ middleValue ((point 4 cut 1024 301+point 4 cut 1024 302)/2)
    have hp : middlePayment 301 = (637313245385:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 301+point 4 cut 1024 302)/2 = (84530159:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84530159:ℝ)/21094400) = (6794240:ℝ)/4291997 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84530159:ℝ)/21094400)-4 = (152559:ℝ)/21094400 by norm_num]
    exact paid_middle_301
  · change middlePayment 302 ≤ middleValue ((point 4 cut 1024 302+point 4 cut 1024 303)/2)
    have hp : middlePayment 302 = (637352581724:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 302+point 4 cut 1024 303)/2 = (16906133:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16906133:ℝ)/4218880) = (33971200:ℝ)/21459479 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16906133:ℝ)/4218880)-4 = (30613:ℝ)/4218880 by norm_num]
    exact paid_middle_302
  · change middlePayment 303 ≤ middleValue ((point 4 cut 1024 303+point 4 cut 1024 304)/2)
    have hp : middlePayment 303 = (637391919588:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 303+point 4 cut 1024 304)/2 = (84531171:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84531171:ℝ)/21094400) = (33971200:ℝ)/21458973 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84531171:ℝ)/21094400)-4 = (153571:ℝ)/21094400 by norm_num]
    exact paid_middle_303
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_018
