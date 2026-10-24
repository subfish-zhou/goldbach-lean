import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints017
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_017 (j : Fin 16) : middlePayment (16*17+j.val) ≤
    middleValue ((point 4 cut 1024 (16*17+j.val)+point 4 cut 1024 (16*17+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 272 ≤ middleValue ((point 4 cut 1024 272+point 4 cut 1024 273)/2)
    have hp : middlePayment 272 = (636173155007:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 272+point 4 cut 1024 273)/2 = (16903097:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16903097:ℝ)/4218880) = (33971200:ℝ)/21474659 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16903097:ℝ)/4218880)-4 = (27577:ℝ)/4218880 by norm_num]
    exact paid_middle_272
  · change middlePayment 273 ≤ middleValue ((point 4 cut 1024 273+point 4 cut 1024 274)/2)
    have hp : middlePayment 273 = (636212447127:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 273+point 4 cut 1024 274)/2 = (84515991:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84515991:ℝ)/21094400) = (33971200:ℝ)/21474153 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84515991:ℝ)/21094400)-4 = (138391:ℝ)/21094400 by norm_num]
    exact paid_middle_273
  · change middlePayment 274 ≤ middleValue ((point 4 cut 1024 274+point 4 cut 1024 275)/2)
    have hp : middlePayment 274 = (636251740770:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 274+point 4 cut 1024 275)/2 = (84516497:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84516497:ℝ)/21094400) = (33971200:ℝ)/21473647 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84516497:ℝ)/21094400)-4 = (138897:ℝ)/21094400 by norm_num]
    exact paid_middle_274
  · change middlePayment 275 ≤ middleValue ((point 4 cut 1024 275+point 4 cut 1024 276)/2)
    have hp : middlePayment 275 = (636291035937:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 275+point 4 cut 1024 276)/2 = (84517003:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84517003:ℝ)/21094400) = (33971200:ℝ)/21473141 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84517003:ℝ)/21094400)-4 = (139403:ℝ)/21094400 by norm_num]
    exact paid_middle_275
  · change middlePayment 276 ≤ middleValue ((point 4 cut 1024 276+point 4 cut 1024 277)/2)
    have hp : middlePayment 276 = (636330332628:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 276+point 4 cut 1024 277)/2 = (84517509:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84517509:ℝ)/21094400) = (6794240:ℝ)/4294527 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84517509:ℝ)/21094400)-4 = (139909:ℝ)/21094400 by norm_num]
    exact paid_middle_276
  · change middlePayment 277 ≤ middleValue ((point 4 cut 1024 277+point 4 cut 1024 278)/2)
    have hp : middlePayment 277 = (636369630843:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 277+point 4 cut 1024 278)/2 = (16903603:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16903603:ℝ)/4218880) = (33971200:ℝ)/21472129 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16903603:ℝ)/4218880)-4 = (28083:ℝ)/4218880 by norm_num]
    exact paid_middle_277
  · change middlePayment 278 ≤ middleValue ((point 4 cut 1024 278+point 4 cut 1024 279)/2)
    have hp : middlePayment 278 = (636408930582:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 278+point 4 cut 1024 279)/2 = (84518521:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84518521:ℝ)/21094400) = (33971200:ℝ)/21471623 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84518521:ℝ)/21094400)-4 = (140921:ℝ)/21094400 by norm_num]
    exact paid_middle_278
  · change middlePayment 279 ≤ middleValue ((point 4 cut 1024 279+point 4 cut 1024 280)/2)
    have hp : middlePayment 279 = (636448231845:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 279+point 4 cut 1024 280)/2 = (84519027:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84519027:ℝ)/21094400) = (33971200:ℝ)/21471117 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84519027:ℝ)/21094400)-4 = (141427:ℝ)/21094400 by norm_num]
    exact paid_middle_279
  · change middlePayment 280 ≤ middleValue ((point 4 cut 1024 280+point 4 cut 1024 281)/2)
    have hp : middlePayment 280 = (636487534632:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 280+point 4 cut 1024 281)/2 = (84519533:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84519533:ℝ)/21094400) = (33971200:ℝ)/21470611 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84519533:ℝ)/21094400)-4 = (141933:ℝ)/21094400 by norm_num]
    exact paid_middle_280
  · change middlePayment 281 ≤ middleValue ((point 4 cut 1024 281+point 4 cut 1024 282)/2)
    have hp : middlePayment 281 = (636526838943:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 281+point 4 cut 1024 282)/2 = (84520039:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84520039:ℝ)/21094400) = (6794240:ℝ)/4294021 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84520039:ℝ)/21094400)-4 = (142439:ℝ)/21094400 by norm_num]
    exact paid_middle_281
  · change middlePayment 282 ≤ middleValue ((point 4 cut 1024 282+point 4 cut 1024 283)/2)
    have hp : middlePayment 282 = (636566144779:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 282+point 4 cut 1024 283)/2 = (16904109:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16904109:ℝ)/4218880) = (33971200:ℝ)/21469599 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16904109:ℝ)/4218880)-4 = (28589:ℝ)/4218880 by norm_num]
    exact paid_middle_282
  · change middlePayment 283 ≤ middleValue ((point 4 cut 1024 283+point 4 cut 1024 284)/2)
    have hp : middlePayment 283 = (636605452139:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 283+point 4 cut 1024 284)/2 = (84521051:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84521051:ℝ)/21094400) = (33971200:ℝ)/21469093 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84521051:ℝ)/21094400)-4 = (143451:ℝ)/21094400 by norm_num]
    exact paid_middle_283
  · change middlePayment 284 ≤ middleValue ((point 4 cut 1024 284+point 4 cut 1024 285)/2)
    have hp : middlePayment 284 = (636644761024:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 284+point 4 cut 1024 285)/2 = (84521557:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84521557:ℝ)/21094400) = (33971200:ℝ)/21468587 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84521557:ℝ)/21094400)-4 = (143957:ℝ)/21094400 by norm_num]
    exact paid_middle_284
  · change middlePayment 285 ≤ middleValue ((point 4 cut 1024 285+point 4 cut 1024 286)/2)
    have hp : middlePayment 285 = (636684071433:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 285+point 4 cut 1024 286)/2 = (84522063:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84522063:ℝ)/21094400) = (33971200:ℝ)/21468081 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84522063:ℝ)/21094400)-4 = (144463:ℝ)/21094400 by norm_num]
    exact paid_middle_285
  · change middlePayment 286 ≤ middleValue ((point 4 cut 1024 286+point 4 cut 1024 287)/2)
    have hp : middlePayment 286 = (636723383367:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 286+point 4 cut 1024 287)/2 = (84522569:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84522569:ℝ)/21094400) = (1358848:ℝ)/858703 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84522569:ℝ)/21094400)-4 = (144969:ℝ)/21094400 by norm_num]
    exact paid_middle_286
  · change middlePayment 287 ≤ middleValue ((point 4 cut 1024 287+point 4 cut 1024 288)/2)
    have hp : middlePayment 287 = (636762696826:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 287+point 4 cut 1024 288)/2 = (3380923:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3380923:ℝ)/843776) = (33971200:ℝ)/21467069 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3380923:ℝ)/843776)-4 = (5819:ℝ)/843776 by norm_num]
    exact paid_middle_287
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_017
