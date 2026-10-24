import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints026
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_026 (j : Fin 16) : middlePayment (16*26+j.val) ≤
    middleValue ((point 4 cut 1024 (16*26+j.val)+point 4 cut 1024 (16*26+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 416 ≤ middleValue ((point 4 cut 1024 416+point 4 cut 1024 417)/2)
    have hp : middlePayment 416 = (641846945860:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 416+point 4 cut 1024 417)/2 = (84588349:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84588349:ℝ)/21094400) = (6794240:ℝ)/4280359 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84588349:ℝ)/21094400)-4 = (210749:ℝ)/21094400 by norm_num]
    exact paid_middle_416
  · change middlePayment 417 ≤ middleValue ((point 4 cut 1024 417+point 4 cut 1024 418)/2)
    have hp : middlePayment 417 = (641886458186:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 417+point 4 cut 1024 418)/2 = (16917771:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16917771:ℝ)/4218880) = (33971200:ℝ)/21401289 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16917771:ℝ)/4218880)-4 = (42251:ℝ)/4218880 by norm_num]
    exact paid_middle_417
  · change middlePayment 418 ≤ middleValue ((point 4 cut 1024 418+point 4 cut 1024 419)/2)
    have hp : middlePayment 418 = (641925972048:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 418+point 4 cut 1024 419)/2 = (84589361:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84589361:ℝ)/21094400) = (33971200:ℝ)/21400783 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84589361:ℝ)/21094400)-4 = (211761:ℝ)/21094400 by norm_num]
    exact paid_middle_418
  · change middlePayment 419 ≤ middleValue ((point 4 cut 1024 419+point 4 cut 1024 420)/2)
    have hp : middlePayment 419 = (641965487444:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 419+point 4 cut 1024 420)/2 = (84589867:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84589867:ℝ)/21094400) = (33971200:ℝ)/21400277 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84589867:ℝ)/21094400)-4 = (212267:ℝ)/21094400 by norm_num]
    exact paid_middle_419
  · change middlePayment 420 ≤ middleValue ((point 4 cut 1024 420+point 4 cut 1024 421)/2)
    have hp : middlePayment 420 = (642005004374:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 420+point 4 cut 1024 421)/2 = (84590373:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84590373:ℝ)/21094400) = (33971200:ℝ)/21399771 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84590373:ℝ)/21094400)-4 = (212773:ℝ)/21094400 by norm_num]
    exact paid_middle_420
  · change middlePayment 421 ≤ middleValue ((point 4 cut 1024 421+point 4 cut 1024 422)/2)
    have hp : middlePayment 421 = (642044522840:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 421+point 4 cut 1024 422)/2 = (84590879:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84590879:ℝ)/21094400) = (6794240:ℝ)/4279853 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84590879:ℝ)/21094400)-4 = (213279:ℝ)/21094400 by norm_num]
    exact paid_middle_421
  · change middlePayment 422 ≤ middleValue ((point 4 cut 1024 422+point 4 cut 1024 423)/2)
    have hp : middlePayment 422 = (642084042842:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 422+point 4 cut 1024 423)/2 = (16918277:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16918277:ℝ)/4218880) = (33971200:ℝ)/21398759 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16918277:ℝ)/4218880)-4 = (42757:ℝ)/4218880 by norm_num]
    exact paid_middle_422
  · change middlePayment 423 ≤ middleValue ((point 4 cut 1024 423+point 4 cut 1024 424)/2)
    have hp : middlePayment 423 = (642123564378:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 423+point 4 cut 1024 424)/2 = (84591891:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84591891:ℝ)/21094400) = (33971200:ℝ)/21398253 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84591891:ℝ)/21094400)-4 = (214291:ℝ)/21094400 by norm_num]
    exact paid_middle_423
  · change middlePayment 424 ≤ middleValue ((point 4 cut 1024 424+point 4 cut 1024 425)/2)
    have hp : middlePayment 424 = (642163087449:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 424+point 4 cut 1024 425)/2 = (84592397:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84592397:ℝ)/21094400) = (33971200:ℝ)/21397747 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84592397:ℝ)/21094400)-4 = (214797:ℝ)/21094400 by norm_num]
    exact paid_middle_424
  · change middlePayment 425 ≤ middleValue ((point 4 cut 1024 425+point 4 cut 1024 426)/2)
    have hp : middlePayment 425 = (642202612056:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 425+point 4 cut 1024 426)/2 = (84592903:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84592903:ℝ)/21094400) = (33971200:ℝ)/21397241 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84592903:ℝ)/21094400)-4 = (215303:ℝ)/21094400 by norm_num]
    exact paid_middle_425
  · change middlePayment 426 ≤ middleValue ((point 4 cut 1024 426+point 4 cut 1024 427)/2)
    have hp : middlePayment 426 = (642242138199:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 426+point 4 cut 1024 427)/2 = (84593409:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84593409:ℝ)/21094400) = (6794240:ℝ)/4279347 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84593409:ℝ)/21094400)-4 = (215809:ℝ)/21094400 by norm_num]
    exact paid_middle_426
  · change middlePayment 427 ≤ middleValue ((point 4 cut 1024 427+point 4 cut 1024 428)/2)
    have hp : middlePayment 427 = (642281665876:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 427+point 4 cut 1024 428)/2 = (16918783:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16918783:ℝ)/4218880) = (33971200:ℝ)/21396229 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16918783:ℝ)/4218880)-4 = (43263:ℝ)/4218880 by norm_num]
    exact paid_middle_427
  · change middlePayment 428 ≤ middleValue ((point 4 cut 1024 428+point 4 cut 1024 429)/2)
    have hp : middlePayment 428 = (642321195090:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 428+point 4 cut 1024 429)/2 = (84594421:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84594421:ℝ)/21094400) = (33971200:ℝ)/21395723 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84594421:ℝ)/21094400)-4 = (216821:ℝ)/21094400 by norm_num]
    exact paid_middle_428
  · change middlePayment 429 ≤ middleValue ((point 4 cut 1024 429+point 4 cut 1024 430)/2)
    have hp : middlePayment 429 = (642360725839:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 429+point 4 cut 1024 430)/2 = (84594927:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84594927:ℝ)/21094400) = (33971200:ℝ)/21395217 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84594927:ℝ)/21094400)-4 = (217327:ℝ)/21094400 by norm_num]
    exact paid_middle_429
  · change middlePayment 430 ≤ middleValue ((point 4 cut 1024 430+point 4 cut 1024 431)/2)
    have hp : middlePayment 430 = (642400258124:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 430+point 4 cut 1024 431)/2 = (84595433:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84595433:ℝ)/21094400) = (33971200:ℝ)/21394711 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84595433:ℝ)/21094400)-4 = (217833:ℝ)/21094400 by norm_num]
    exact paid_middle_430
  · change middlePayment 431 ≤ middleValue ((point 4 cut 1024 431+point 4 cut 1024 432)/2)
    have hp : middlePayment 431 = (642439791944:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 431+point 4 cut 1024 432)/2 = (84595939:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84595939:ℝ)/21094400) = (6794240:ℝ)/4278841 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84595939:ℝ)/21094400)-4 = (218339:ℝ)/21094400 by norm_num]
    exact paid_middle_431
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_026
