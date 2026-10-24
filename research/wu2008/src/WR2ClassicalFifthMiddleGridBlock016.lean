import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints016
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_016 (j : Fin 16) : middlePayment (16*16+j.val) ≤
    middleValue ((point 4 cut 1024 (16*16+j.val)+point 4 cut 1024 (16*16+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 256 ≤ middleValue ((point 4 cut 1024 256+point 4 cut 1024 257)/2)
    have hp : middlePayment 256 = (635544688258:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 256+point 4 cut 1024 257)/2 = (84507389:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84507389:ℝ)/21094400) = (6794240:ℝ)/4296551 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84507389:ℝ)/21094400)-4 = (129789:ℝ)/21094400 by norm_num]
    exact paid_middle_256
  · change middlePayment 257 ≤ middleValue ((point 4 cut 1024 257+point 4 cut 1024 258)/2)
    have hp : middlePayment 257 = (635583956008:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 257+point 4 cut 1024 258)/2 = (164093:ℝ)/40960 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164093:ℝ)/40960) = (33971200:ℝ)/21482249 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((164093:ℝ)/40960)-4 = (253:ℝ)/40960 by norm_num]
    exact paid_middle_257
  · change middlePayment 258 ≤ middleValue ((point 4 cut 1024 258+point 4 cut 1024 259)/2)
    have hp : middlePayment 258 = (635623225281:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 258+point 4 cut 1024 259)/2 = (84508401:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84508401:ℝ)/21094400) = (33971200:ℝ)/21481743 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84508401:ℝ)/21094400)-4 = (130801:ℝ)/21094400 by norm_num]
    exact paid_middle_258
  · change middlePayment 259 ≤ middleValue ((point 4 cut 1024 259+point 4 cut 1024 260)/2)
    have hp : middlePayment 259 = (635662496077:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 259+point 4 cut 1024 260)/2 = (84508907:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84508907:ℝ)/21094400) = (33971200:ℝ)/21481237 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84508907:ℝ)/21094400)-4 = (131307:ℝ)/21094400 by norm_num]
    exact paid_middle_259
  · change middlePayment 260 ≤ middleValue ((point 4 cut 1024 260+point 4 cut 1024 261)/2)
    have hp : middlePayment 260 = (635701768395:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 260+point 4 cut 1024 261)/2 = (84509413:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84509413:ℝ)/21094400) = (33971200:ℝ)/21480731 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84509413:ℝ)/21094400)-4 = (131813:ℝ)/21094400 by norm_num]
    exact paid_middle_260
  · change middlePayment 261 ≤ middleValue ((point 4 cut 1024 261+point 4 cut 1024 262)/2)
    have hp : middlePayment 261 = (635741042236:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 261+point 4 cut 1024 262)/2 = (84509919:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84509919:ℝ)/21094400) = (1358848:ℝ)/859209 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84509919:ℝ)/21094400)-4 = (132319:ℝ)/21094400 by norm_num]
    exact paid_middle_261
  · change middlePayment 262 ≤ middleValue ((point 4 cut 1024 262+point 4 cut 1024 263)/2)
    have hp : middlePayment 262 = (635780317599:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 262+point 4 cut 1024 263)/2 = (3380417:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3380417:ℝ)/843776) = (33971200:ℝ)/21479719 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3380417:ℝ)/843776)-4 = (5313:ℝ)/843776 by norm_num]
    exact paid_middle_262
  · change middlePayment 263 ≤ middleValue ((point 4 cut 1024 263+point 4 cut 1024 264)/2)
    have hp : middlePayment 263 = (635819594486:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 263+point 4 cut 1024 264)/2 = (84510931:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84510931:ℝ)/21094400) = (33971200:ℝ)/21479213 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84510931:ℝ)/21094400)-4 = (133331:ℝ)/21094400 by norm_num]
    exact paid_middle_263
  · change middlePayment 264 ≤ middleValue ((point 4 cut 1024 264+point 4 cut 1024 265)/2)
    have hp : middlePayment 264 = (635858872895:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 264+point 4 cut 1024 265)/2 = (84511437:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84511437:ℝ)/21094400) = (33971200:ℝ)/21478707 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84511437:ℝ)/21094400)-4 = (133837:ℝ)/21094400 by norm_num]
    exact paid_middle_264
  · change middlePayment 265 ≤ middleValue ((point 4 cut 1024 265+point 4 cut 1024 266)/2)
    have hp : middlePayment 265 = (635898152828:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 265+point 4 cut 1024 266)/2 = (84511943:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84511943:ℝ)/21094400) = (33971200:ℝ)/21478201 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84511943:ℝ)/21094400)-4 = (134343:ℝ)/21094400 by norm_num]
    exact paid_middle_265
  · change middlePayment 266 ≤ middleValue ((point 4 cut 1024 266+point 4 cut 1024 267)/2)
    have hp : middlePayment 266 = (635937434283:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 266+point 4 cut 1024 267)/2 = (84512449:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84512449:ℝ)/21094400) = (6794240:ℝ)/4295539 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84512449:ℝ)/21094400)-4 = (134849:ℝ)/21094400 by norm_num]
    exact paid_middle_266
  · change middlePayment 267 ≤ middleValue ((point 4 cut 1024 267+point 4 cut 1024 268)/2)
    have hp : middlePayment 267 = (635976717262:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 267+point 4 cut 1024 268)/2 = (16902591:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16902591:ℝ)/4218880) = (33971200:ℝ)/21477189 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16902591:ℝ)/4218880)-4 = (27071:ℝ)/4218880 by norm_num]
    exact paid_middle_267
  · change middlePayment 268 ≤ middleValue ((point 4 cut 1024 268+point 4 cut 1024 269)/2)
    have hp : middlePayment 268 = (636016001764:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 268+point 4 cut 1024 269)/2 = (84513461:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84513461:ℝ)/21094400) = (33971200:ℝ)/21476683 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84513461:ℝ)/21094400)-4 = (135861:ℝ)/21094400 by norm_num]
    exact paid_middle_268
  · change middlePayment 269 ≤ middleValue ((point 4 cut 1024 269+point 4 cut 1024 270)/2)
    have hp : middlePayment 269 = (636055287790:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 269+point 4 cut 1024 270)/2 = (84513967:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84513967:ℝ)/21094400) = (33971200:ℝ)/21476177 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84513967:ℝ)/21094400)-4 = (136367:ℝ)/21094400 by norm_num]
    exact paid_middle_269
  · change middlePayment 270 ≤ middleValue ((point 4 cut 1024 270+point 4 cut 1024 271)/2)
    have hp : middlePayment 270 = (636094575339:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 270+point 4 cut 1024 271)/2 = (84514473:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84514473:ℝ)/21094400) = (33971200:ℝ)/21475671 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84514473:ℝ)/21094400)-4 = (136873:ℝ)/21094400 by norm_num]
    exact paid_middle_270
  · change middlePayment 271 ≤ middleValue ((point 4 cut 1024 271+point 4 cut 1024 272)/2)
    have hp : middlePayment 271 = (636133864411:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 271+point 4 cut 1024 272)/2 = (84514979:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84514979:ℝ)/21094400) = (6794240:ℝ)/4295033 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84514979:ℝ)/21094400)-4 = (137379:ℝ)/21094400 by norm_num]
    exact paid_middle_271
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_016
