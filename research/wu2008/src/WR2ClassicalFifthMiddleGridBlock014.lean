import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints014
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_014 (j : Fin 16) : middlePayment (16*14+j.val) ≤
    middleValue ((point 4 cut 1024 (16*14+j.val)+point 4 cut 1024 (16*14+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 224 ≤ middleValue ((point 4 cut 1024 224+point 4 cut 1024 225)/2)
    have hp : middlePayment 224 = (634288923665:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 224+point 4 cut 1024 225)/2 = (84491197:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84491197:ℝ)/21094400) = (33971200:ℝ)/21498947 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84491197:ℝ)/21094400)-4 = (113597:ℝ)/21094400 by norm_num]
    exact paid_middle_224
  · change middlePayment 225 ≤ middleValue ((point 4 cut 1024 225+point 4 cut 1024 226)/2)
    have hp : middlePayment 225 = (634328142736:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 225+point 4 cut 1024 226)/2 = (84491703:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84491703:ℝ)/21094400) = (33971200:ℝ)/21498441 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84491703:ℝ)/21094400)-4 = (114103:ℝ)/21094400 by norm_num]
    exact paid_middle_225
  · change middlePayment 226 ≤ middleValue ((point 4 cut 1024 226+point 4 cut 1024 227)/2)
    have hp : middlePayment 226 = (634367363327:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 226+point 4 cut 1024 227)/2 = (84492209:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84492209:ℝ)/21094400) = (6794240:ℝ)/4299587 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84492209:ℝ)/21094400)-4 = (114609:ℝ)/21094400 by norm_num]
    exact paid_middle_226
  · change middlePayment 227 ≤ middleValue ((point 4 cut 1024 227+point 4 cut 1024 228)/2)
    have hp : middlePayment 227 = (634406585438:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 227+point 4 cut 1024 228)/2 = (16898543:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16898543:ℝ)/4218880) = (33971200:ℝ)/21497429 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16898543:ℝ)/4218880)-4 = (23023:ℝ)/4218880 by norm_num]
    exact paid_middle_227
  · change middlePayment 228 ≤ middleValue ((point 4 cut 1024 228+point 4 cut 1024 229)/2)
    have hp : middlePayment 228 = (634445809069:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 228+point 4 cut 1024 229)/2 = (84493221:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84493221:ℝ)/21094400) = (33971200:ℝ)/21496923 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84493221:ℝ)/21094400)-4 = (115621:ℝ)/21094400 by norm_num]
    exact paid_middle_228
  · change middlePayment 229 ≤ middleValue ((point 4 cut 1024 229+point 4 cut 1024 230)/2)
    have hp : middlePayment 229 = (634485034221:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 229+point 4 cut 1024 230)/2 = (84493727:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84493727:ℝ)/21094400) = (33971200:ℝ)/21496417 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84493727:ℝ)/21094400)-4 = (116127:ℝ)/21094400 by norm_num]
    exact paid_middle_229
  · change middlePayment 230 ≤ middleValue ((point 4 cut 1024 230+point 4 cut 1024 231)/2)
    have hp : middlePayment 230 = (634524260893:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 230+point 4 cut 1024 231)/2 = (84494233:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84494233:ℝ)/21094400) = (33971200:ℝ)/21495911 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84494233:ℝ)/21094400)-4 = (116633:ℝ)/21094400 by norm_num]
    exact paid_middle_230
  · change middlePayment 231 ≤ middleValue ((point 4 cut 1024 231+point 4 cut 1024 232)/2)
    have hp : middlePayment 231 = (634563489085:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 231+point 4 cut 1024 232)/2 = (84494739:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84494739:ℝ)/21094400) = (6794240:ℝ)/4299081 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84494739:ℝ)/21094400)-4 = (117139:ℝ)/21094400 by norm_num]
    exact paid_middle_231
  · change middlePayment 232 ≤ middleValue ((point 4 cut 1024 232+point 4 cut 1024 233)/2)
    have hp : middlePayment 232 = (634602718798:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 232+point 4 cut 1024 233)/2 = (16899049:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16899049:ℝ)/4218880) = (33971200:ℝ)/21494899 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16899049:ℝ)/4218880)-4 = (23529:ℝ)/4218880 by norm_num]
    exact paid_middle_232
  · change middlePayment 233 ≤ middleValue ((point 4 cut 1024 233+point 4 cut 1024 234)/2)
    have hp : middlePayment 233 = (634641950031:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 233+point 4 cut 1024 234)/2 = (84495751:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84495751:ℝ)/21094400) = (33971200:ℝ)/21494393 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84495751:ℝ)/21094400)-4 = (118151:ℝ)/21094400 by norm_num]
    exact paid_middle_233
  · change middlePayment 234 ≤ middleValue ((point 4 cut 1024 234+point 4 cut 1024 235)/2)
    have hp : middlePayment 234 = (634681182785:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 234+point 4 cut 1024 235)/2 = (84496257:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84496257:ℝ)/21094400) = (33971200:ℝ)/21493887 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84496257:ℝ)/21094400)-4 = (118657:ℝ)/21094400 by norm_num]
    exact paid_middle_234
  · change middlePayment 235 ≤ middleValue ((point 4 cut 1024 235+point 4 cut 1024 236)/2)
    have hp : middlePayment 235 = (634720417060:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 235+point 4 cut 1024 236)/2 = (84496763:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84496763:ℝ)/21094400) = (33971200:ℝ)/21493381 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84496763:ℝ)/21094400)-4 = (119163:ℝ)/21094400 by norm_num]
    exact paid_middle_235
  · change middlePayment 236 ≤ middleValue ((point 4 cut 1024 236+point 4 cut 1024 237)/2)
    have hp : middlePayment 236 = (634759652856:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 236+point 4 cut 1024 237)/2 = (84497269:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84497269:ℝ)/21094400) = (1358848:ℝ)/859715 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84497269:ℝ)/21094400)-4 = (119669:ℝ)/21094400 by norm_num]
    exact paid_middle_236
  · change middlePayment 237 ≤ middleValue ((point 4 cut 1024 237+point 4 cut 1024 238)/2)
    have hp : middlePayment 237 = (634798890172:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 237+point 4 cut 1024 238)/2 = (3379911:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3379911:ℝ)/843776) = (33971200:ℝ)/21492369 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3379911:ℝ)/843776)-4 = (4807:ℝ)/843776 by norm_num]
    exact paid_middle_237
  · change middlePayment 238 ≤ middleValue ((point 4 cut 1024 238+point 4 cut 1024 239)/2)
    have hp : middlePayment 238 = (634838129010:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 238+point 4 cut 1024 239)/2 = (84498281:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84498281:ℝ)/21094400) = (33971200:ℝ)/21491863 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84498281:ℝ)/21094400)-4 = (120681:ℝ)/21094400 by norm_num]
    exact paid_middle_238
  · change middlePayment 239 ≤ middleValue ((point 4 cut 1024 239+point 4 cut 1024 240)/2)
    have hp : middlePayment 239 = (634877369368:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 239+point 4 cut 1024 240)/2 = (84498787:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84498787:ℝ)/21094400) = (33971200:ℝ)/21491357 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84498787:ℝ)/21094400)-4 = (121187:ℝ)/21094400 by norm_num]
    exact paid_middle_239
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_014
