import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints021
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_021 (j : Fin 16) : middlePayment (16*21+j.val) ≤
    middleValue ((point 4 cut 1024 (16*21+j.val)+point 4 cut 1024 (16*21+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 336 ≤ middleValue ((point 4 cut 1024 336+point 4 cut 1024 337)/2)
    have hp : middlePayment 336 = (638690925674:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 336+point 4 cut 1024 337)/2 = (84547869:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84547869:ℝ)/21094400) = (1358848:ℝ)/857691 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84547869:ℝ)/21094400)-4 = (170269:ℝ)/21094400 by norm_num]
    exact paid_middle_336
  · change middlePayment 337 ≤ middleValue ((point 4 cut 1024 337+point 4 cut 1024 338)/2)
    have hp : middlePayment 337 = (638730315466:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 337+point 4 cut 1024 338)/2 = (3381935:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3381935:ℝ)/843776) = (33971200:ℝ)/21441769 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3381935:ℝ)/843776)-4 = (6831:ℝ)/843776 by norm_num]
    exact paid_middle_337
  · change middlePayment 338 ≤ middleValue ((point 4 cut 1024 338+point 4 cut 1024 339)/2)
    have hp : middlePayment 338 = (638769706787:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 338+point 4 cut 1024 339)/2 = (84548881:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84548881:ℝ)/21094400) = (33971200:ℝ)/21441263 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84548881:ℝ)/21094400)-4 = (171281:ℝ)/21094400 by norm_num]
    exact paid_middle_338
  · change middlePayment 339 ≤ middleValue ((point 4 cut 1024 339+point 4 cut 1024 340)/2)
    have hp : middlePayment 339 = (638809099637:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 339+point 4 cut 1024 340)/2 = (84549387:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84549387:ℝ)/21094400) = (33971200:ℝ)/21440757 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84549387:ℝ)/21094400)-4 = (171787:ℝ)/21094400 by norm_num]
    exact paid_middle_339
  · change middlePayment 340 ≤ middleValue ((point 4 cut 1024 340+point 4 cut 1024 341)/2)
    have hp : middlePayment 340 = (638848494015:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 340+point 4 cut 1024 341)/2 = (84549893:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84549893:ℝ)/21094400) = (33971200:ℝ)/21440251 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84549893:ℝ)/21094400)-4 = (172293:ℝ)/21094400 by norm_num]
    exact paid_middle_340
  · change middlePayment 341 ≤ middleValue ((point 4 cut 1024 341+point 4 cut 1024 342)/2)
    have hp : middlePayment 341 = (638887889922:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 341+point 4 cut 1024 342)/2 = (84550399:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84550399:ℝ)/21094400) = (6794240:ℝ)/4287949 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84550399:ℝ)/21094400)-4 = (172799:ℝ)/21094400 by norm_num]
    exact paid_middle_341
  · change middlePayment 342 ≤ middleValue ((point 4 cut 1024 342+point 4 cut 1024 343)/2)
    have hp : middlePayment 342 = (638927287359:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 342+point 4 cut 1024 343)/2 = (16910181:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16910181:ℝ)/4218880) = (33971200:ℝ)/21439239 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16910181:ℝ)/4218880)-4 = (34661:ℝ)/4218880 by norm_num]
    exact paid_middle_342
  · change middlePayment 343 ≤ middleValue ((point 4 cut 1024 343+point 4 cut 1024 344)/2)
    have hp : middlePayment 343 = (638966686324:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 343+point 4 cut 1024 344)/2 = (84551411:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84551411:ℝ)/21094400) = (33971200:ℝ)/21438733 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84551411:ℝ)/21094400)-4 = (173811:ℝ)/21094400 by norm_num]
    exact paid_middle_343
  · change middlePayment 344 ≤ middleValue ((point 4 cut 1024 344+point 4 cut 1024 345)/2)
    have hp : middlePayment 344 = (639006086818:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 344+point 4 cut 1024 345)/2 = (84551917:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84551917:ℝ)/21094400) = (33971200:ℝ)/21438227 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84551917:ℝ)/21094400)-4 = (174317:ℝ)/21094400 by norm_num]
    exact paid_middle_344
  · change middlePayment 345 ≤ middleValue ((point 4 cut 1024 345+point 4 cut 1024 346)/2)
    have hp : middlePayment 345 = (639045488842:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 345+point 4 cut 1024 346)/2 = (84552423:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84552423:ℝ)/21094400) = (33971200:ℝ)/21437721 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84552423:ℝ)/21094400)-4 = (174823:ℝ)/21094400 by norm_num]
    exact paid_middle_345
  · change middlePayment 346 ≤ middleValue ((point 4 cut 1024 346+point 4 cut 1024 347)/2)
    have hp : middlePayment 346 = (639084892394:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 346+point 4 cut 1024 347)/2 = (84552929:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84552929:ℝ)/21094400) = (6794240:ℝ)/4287443 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84552929:ℝ)/21094400)-4 = (175329:ℝ)/21094400 by norm_num]
    exact paid_middle_346
  · change middlePayment 347 ≤ middleValue ((point 4 cut 1024 347+point 4 cut 1024 348)/2)
    have hp : middlePayment 347 = (639124297476:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 347+point 4 cut 1024 348)/2 = (16910687:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16910687:ℝ)/4218880) = (33971200:ℝ)/21436709 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16910687:ℝ)/4218880)-4 = (35167:ℝ)/4218880 by norm_num]
    exact paid_middle_347
  · change middlePayment 348 ≤ middleValue ((point 4 cut 1024 348+point 4 cut 1024 349)/2)
    have hp : middlePayment 348 = (639163704088:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 348+point 4 cut 1024 349)/2 = (84553941:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84553941:ℝ)/21094400) = (33971200:ℝ)/21436203 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84553941:ℝ)/21094400)-4 = (176341:ℝ)/21094400 by norm_num]
    exact paid_middle_348
  · change middlePayment 349 ≤ middleValue ((point 4 cut 1024 349+point 4 cut 1024 350)/2)
    have hp : middlePayment 349 = (639203112229:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 349+point 4 cut 1024 350)/2 = (84554447:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84554447:ℝ)/21094400) = (33971200:ℝ)/21435697 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84554447:ℝ)/21094400)-4 = (176847:ℝ)/21094400 by norm_num]
    exact paid_middle_349
  · change middlePayment 350 ≤ middleValue ((point 4 cut 1024 350+point 4 cut 1024 351)/2)
    have hp : middlePayment 350 = (639242521899:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 350+point 4 cut 1024 351)/2 = (84554953:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84554953:ℝ)/21094400) = (33971200:ℝ)/21435191 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84554953:ℝ)/21094400)-4 = (177353:ℝ)/21094400 by norm_num]
    exact paid_middle_350
  · change middlePayment 351 ≤ middleValue ((point 4 cut 1024 351+point 4 cut 1024 352)/2)
    have hp : middlePayment 351 = (639281933099:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 351+point 4 cut 1024 352)/2 = (84555459:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84555459:ℝ)/21094400) = (6794240:ℝ)/4286937 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84555459:ℝ)/21094400)-4 = (177859:ℝ)/21094400 by norm_num]
    exact paid_middle_351
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_021
