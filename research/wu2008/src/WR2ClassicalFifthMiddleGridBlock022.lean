import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints022
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_022 (j : Fin 16) : middlePayment (16*22+j.val) ≤
    middleValue ((point 4 cut 1024 (16*22+j.val)+point 4 cut 1024 (16*22+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 352 ≤ middleValue ((point 4 cut 1024 352+point 4 cut 1024 353)/2)
    have hp : middlePayment 352 = (639321345829:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 352+point 4 cut 1024 353)/2 = (16911193:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16911193:ℝ)/4218880) = (33971200:ℝ)/21434179 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16911193:ℝ)/4218880)-4 = (35673:ℝ)/4218880 by norm_num]
    exact paid_middle_352
  · change middlePayment 353 ≤ middleValue ((point 4 cut 1024 353+point 4 cut 1024 354)/2)
    have hp : middlePayment 353 = (639360760089:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 353+point 4 cut 1024 354)/2 = (84556471:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84556471:ℝ)/21094400) = (33971200:ℝ)/21433673 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84556471:ℝ)/21094400)-4 = (178871:ℝ)/21094400 by norm_num]
    exact paid_middle_353
  · change middlePayment 354 ≤ middleValue ((point 4 cut 1024 354+point 4 cut 1024 355)/2)
    have hp : middlePayment 354 = (639400175878:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 354+point 4 cut 1024 355)/2 = (84556977:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84556977:ℝ)/21094400) = (33971200:ℝ)/21433167 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84556977:ℝ)/21094400)-4 = (179377:ℝ)/21094400 by norm_num]
    exact paid_middle_354
  · change middlePayment 355 ≤ middleValue ((point 4 cut 1024 355+point 4 cut 1024 356)/2)
    have hp : middlePayment 355 = (639439593198:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 355+point 4 cut 1024 356)/2 = (84557483:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84557483:ℝ)/21094400) = (33971200:ℝ)/21432661 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84557483:ℝ)/21094400)-4 = (179883:ℝ)/21094400 by norm_num]
    exact paid_middle_355
  · change middlePayment 356 ≤ middleValue ((point 4 cut 1024 356+point 4 cut 1024 357)/2)
    have hp : middlePayment 356 = (639479012047:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 356+point 4 cut 1024 357)/2 = (84557989:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84557989:ℝ)/21094400) = (6794240:ℝ)/4286431 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84557989:ℝ)/21094400)-4 = (180389:ℝ)/21094400 by norm_num]
    exact paid_middle_356
  · change middlePayment 357 ≤ middleValue ((point 4 cut 1024 357+point 4 cut 1024 358)/2)
    have hp : middlePayment 357 = (639518432427:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 357+point 4 cut 1024 358)/2 = (16911699:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16911699:ℝ)/4218880) = (33971200:ℝ)/21431649 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16911699:ℝ)/4218880)-4 = (36179:ℝ)/4218880 by norm_num]
    exact paid_middle_357
  · change middlePayment 358 ≤ middleValue ((point 4 cut 1024 358+point 4 cut 1024 359)/2)
    have hp : middlePayment 358 = (639557854336:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 358+point 4 cut 1024 359)/2 = (84559001:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84559001:ℝ)/21094400) = (33971200:ℝ)/21431143 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84559001:ℝ)/21094400)-4 = (181401:ℝ)/21094400 by norm_num]
    exact paid_middle_358
  · change middlePayment 359 ≤ middleValue ((point 4 cut 1024 359+point 4 cut 1024 360)/2)
    have hp : middlePayment 359 = (639597277776:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 359+point 4 cut 1024 360)/2 = (84559507:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84559507:ℝ)/21094400) = (33971200:ℝ)/21430637 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84559507:ℝ)/21094400)-4 = (181907:ℝ)/21094400 by norm_num]
    exact paid_middle_359
  · change middlePayment 360 ≤ middleValue ((point 4 cut 1024 360+point 4 cut 1024 361)/2)
    have hp : middlePayment 360 = (639636702747:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 360+point 4 cut 1024 361)/2 = (820971:ℝ)/204800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((820971:ℝ)/204800) = (33971200:ℝ)/21430131 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((820971:ℝ)/204800)-4 = (1771:ℝ)/204800 by norm_num]
    exact paid_middle_360
  · change middlePayment 361 ≤ middleValue ((point 4 cut 1024 361+point 4 cut 1024 362)/2)
    have hp : middlePayment 361 = (639676129247:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 361+point 4 cut 1024 362)/2 = (84560519:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84560519:ℝ)/21094400) = (1358848:ℝ)/857185 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84560519:ℝ)/21094400)-4 = (182919:ℝ)/21094400 by norm_num]
    exact paid_middle_361
  · change middlePayment 362 ≤ middleValue ((point 4 cut 1024 362+point 4 cut 1024 363)/2)
    have hp : middlePayment 362 = (639715557278:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 362+point 4 cut 1024 363)/2 = (3382441:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3382441:ℝ)/843776) = (33971200:ℝ)/21429119 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3382441:ℝ)/843776)-4 = (7337:ℝ)/843776 by norm_num]
    exact paid_middle_362
  · change middlePayment 363 ≤ middleValue ((point 4 cut 1024 363+point 4 cut 1024 364)/2)
    have hp : middlePayment 363 = (639754986840:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 363+point 4 cut 1024 364)/2 = (84561531:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84561531:ℝ)/21094400) = (33971200:ℝ)/21428613 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84561531:ℝ)/21094400)-4 = (183931:ℝ)/21094400 by norm_num]
    exact paid_middle_363
  · change middlePayment 364 ≤ middleValue ((point 4 cut 1024 364+point 4 cut 1024 365)/2)
    have hp : middlePayment 364 = (639794417932:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 364+point 4 cut 1024 365)/2 = (84562037:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84562037:ℝ)/21094400) = (33971200:ℝ)/21428107 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84562037:ℝ)/21094400)-4 = (184437:ℝ)/21094400 by norm_num]
    exact paid_middle_364
  · change middlePayment 365 ≤ middleValue ((point 4 cut 1024 365+point 4 cut 1024 366)/2)
    have hp : middlePayment 365 = (639833850556:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 365+point 4 cut 1024 366)/2 = (84562543:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84562543:ℝ)/21094400) = (33971200:ℝ)/21427601 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84562543:ℝ)/21094400)-4 = (184943:ℝ)/21094400 by norm_num]
    exact paid_middle_365
  · change middlePayment 366 ≤ middleValue ((point 4 cut 1024 366+point 4 cut 1024 367)/2)
    have hp : middlePayment 366 = (639873284709:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 366+point 4 cut 1024 367)/2 = (84563049:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84563049:ℝ)/21094400) = (6794240:ℝ)/4285419 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84563049:ℝ)/21094400)-4 = (185449:ℝ)/21094400 by norm_num]
    exact paid_middle_366
  · change middlePayment 367 ≤ middleValue ((point 4 cut 1024 367+point 4 cut 1024 368)/2)
    have hp : middlePayment 367 = (639912720394:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 367+point 4 cut 1024 368)/2 = (16912711:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16912711:ℝ)/4218880) = (33971200:ℝ)/21426589 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16912711:ℝ)/4218880)-4 = (37191:ℝ)/4218880 by norm_num]
    exact paid_middle_367
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_022
