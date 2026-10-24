import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints024
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_024 (j : Fin 16) : middlePayment (16*24+j.val) ≤
    middleValue ((point 4 cut 1024 (16*24+j.val)+point 4 cut 1024 (16*24+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 384 ≤ middleValue ((point 4 cut 1024 384+point 4 cut 1024 385)/2)
    have hp : middlePayment 384 = (640583361331:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 384+point 4 cut 1024 385)/2 = (84572157:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84572157:ℝ)/21094400) = (33971200:ℝ)/21417987 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84572157:ℝ)/21094400)-4 = (194557:ℝ)/21094400 by norm_num]
    exact paid_middle_384
  · change middlePayment 385 ≤ middleValue ((point 4 cut 1024 385+point 4 cut 1024 386)/2)
    have hp : middlePayment 385 = (640622824585:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 385+point 4 cut 1024 386)/2 = (84572663:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84572663:ℝ)/21094400) = (33971200:ℝ)/21417481 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84572663:ℝ)/21094400)-4 = (195063:ℝ)/21094400 by norm_num]
    exact paid_middle_385
  · change middlePayment 386 ≤ middleValue ((point 4 cut 1024 386+point 4 cut 1024 387)/2)
    have hp : middlePayment 386 = (640662289370:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 386+point 4 cut 1024 387)/2 = (84573169:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84573169:ℝ)/21094400) = (1358848:ℝ)/856679 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84573169:ℝ)/21094400)-4 = (195569:ℝ)/21094400 by norm_num]
    exact paid_middle_386
  · change middlePayment 387 ≤ middleValue ((point 4 cut 1024 387+point 4 cut 1024 388)/2)
    have hp : middlePayment 387 = (640701755689:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 387+point 4 cut 1024 388)/2 = (3382947:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3382947:ℝ)/843776) = (33971200:ℝ)/21416469 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3382947:ℝ)/843776)-4 = (7843:ℝ)/843776 by norm_num]
    exact paid_middle_387
  · change middlePayment 388 ≤ middleValue ((point 4 cut 1024 388+point 4 cut 1024 389)/2)
    have hp : middlePayment 388 = (640741223539:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 388+point 4 cut 1024 389)/2 = (84574181:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84574181:ℝ)/21094400) = (33971200:ℝ)/21415963 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84574181:ℝ)/21094400)-4 = (196581:ℝ)/21094400 by norm_num]
    exact paid_middle_388
  · change middlePayment 389 ≤ middleValue ((point 4 cut 1024 389+point 4 cut 1024 390)/2)
    have hp : middlePayment 389 = (640780692922:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 389+point 4 cut 1024 390)/2 = (84574687:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84574687:ℝ)/21094400) = (33971200:ℝ)/21415457 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84574687:ℝ)/21094400)-4 = (197087:ℝ)/21094400 by norm_num]
    exact paid_middle_389
  · change middlePayment 390 ≤ middleValue ((point 4 cut 1024 390+point 4 cut 1024 391)/2)
    have hp : middlePayment 390 = (640820163838:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 390+point 4 cut 1024 391)/2 = (84575193:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84575193:ℝ)/21094400) = (33971200:ℝ)/21414951 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84575193:ℝ)/21094400)-4 = (197593:ℝ)/21094400 by norm_num]
    exact paid_middle_390
  · change middlePayment 391 ≤ middleValue ((point 4 cut 1024 391+point 4 cut 1024 392)/2)
    have hp : middlePayment 391 = (640859636287:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 391+point 4 cut 1024 392)/2 = (84575699:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84575699:ℝ)/21094400) = (6794240:ℝ)/4282889 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84575699:ℝ)/21094400)-4 = (198099:ℝ)/21094400 by norm_num]
    exact paid_middle_391
  · change middlePayment 392 ≤ middleValue ((point 4 cut 1024 392+point 4 cut 1024 393)/2)
    have hp : middlePayment 392 = (640899110268:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 392+point 4 cut 1024 393)/2 = (16915241:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16915241:ℝ)/4218880) = (33971200:ℝ)/21413939 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16915241:ℝ)/4218880)-4 = (39721:ℝ)/4218880 by norm_num]
    exact paid_middle_392
  · change middlePayment 393 ≤ middleValue ((point 4 cut 1024 393+point 4 cut 1024 394)/2)
    have hp : middlePayment 393 = (640938585783:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 393+point 4 cut 1024 394)/2 = (84576711:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84576711:ℝ)/21094400) = (33971200:ℝ)/21413433 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84576711:ℝ)/21094400)-4 = (199111:ℝ)/21094400 by norm_num]
    exact paid_middle_393
  · change middlePayment 394 ≤ middleValue ((point 4 cut 1024 394+point 4 cut 1024 395)/2)
    have hp : middlePayment 394 = (640978062830:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 394+point 4 cut 1024 395)/2 = (84577217:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84577217:ℝ)/21094400) = (33971200:ℝ)/21412927 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84577217:ℝ)/21094400)-4 = (199617:ℝ)/21094400 by norm_num]
    exact paid_middle_394
  · change middlePayment 395 ≤ middleValue ((point 4 cut 1024 395+point 4 cut 1024 396)/2)
    have hp : middlePayment 395 = (641017541410:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 395+point 4 cut 1024 396)/2 = (84577723:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84577723:ℝ)/21094400) = (33971200:ℝ)/21412421 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84577723:ℝ)/21094400)-4 = (200123:ℝ)/21094400 by norm_num]
    exact paid_middle_395
  · change middlePayment 396 ≤ middleValue ((point 4 cut 1024 396+point 4 cut 1024 397)/2)
    have hp : middlePayment 396 = (641057021523:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 396+point 4 cut 1024 397)/2 = (84578229:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84578229:ℝ)/21094400) = (6794240:ℝ)/4282383 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84578229:ℝ)/21094400)-4 = (200629:ℝ)/21094400 by norm_num]
    exact paid_middle_396
  · change middlePayment 397 ≤ middleValue ((point 4 cut 1024 397+point 4 cut 1024 398)/2)
    have hp : middlePayment 397 = (641096503170:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 397+point 4 cut 1024 398)/2 = (16915747:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16915747:ℝ)/4218880) = (33971200:ℝ)/21411409 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16915747:ℝ)/4218880)-4 = (40227:ℝ)/4218880 by norm_num]
    exact paid_middle_397
  · change middlePayment 398 ≤ middleValue ((point 4 cut 1024 398+point 4 cut 1024 399)/2)
    have hp : middlePayment 398 = (641135986350:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 398+point 4 cut 1024 399)/2 = (84579241:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84579241:ℝ)/21094400) = (33971200:ℝ)/21410903 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84579241:ℝ)/21094400)-4 = (201641:ℝ)/21094400 by norm_num]
    exact paid_middle_398
  · change middlePayment 399 ≤ middleValue ((point 4 cut 1024 399+point 4 cut 1024 400)/2)
    have hp : middlePayment 399 = (641175471063:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 399+point 4 cut 1024 400)/2 = (84579747:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84579747:ℝ)/21094400) = (33971200:ℝ)/21410397 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84579747:ℝ)/21094400)-4 = (202147:ℝ)/21094400 by norm_num]
    exact paid_middle_399
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_024
