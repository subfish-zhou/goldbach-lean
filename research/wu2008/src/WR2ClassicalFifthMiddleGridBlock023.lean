import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints023
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_023 (j : Fin 16) : middlePayment (16*23+j.val) ≤
    middleValue ((point 4 cut 1024 (16*23+j.val)+point 4 cut 1024 (16*23+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 368 ≤ middleValue ((point 4 cut 1024 368+point 4 cut 1024 369)/2)
    have hp : middlePayment 368 = (639952157610:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 368+point 4 cut 1024 369)/2 = (84564061:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84564061:ℝ)/21094400) = (33971200:ℝ)/21426083 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84564061:ℝ)/21094400)-4 = (186461:ℝ)/21094400 by norm_num]
    exact paid_middle_368
  · change middlePayment 369 ≤ middleValue ((point 4 cut 1024 369+point 4 cut 1024 370)/2)
    have hp : middlePayment 369 = (639991596356:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 369+point 4 cut 1024 370)/2 = (84564567:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84564567:ℝ)/21094400) = (33971200:ℝ)/21425577 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84564567:ℝ)/21094400)-4 = (186967:ℝ)/21094400 by norm_num]
    exact paid_middle_369
  · change middlePayment 370 ≤ middleValue ((point 4 cut 1024 370+point 4 cut 1024 371)/2)
    have hp : middlePayment 370 = (640031036634:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 370+point 4 cut 1024 371)/2 = (84565073:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84565073:ℝ)/21094400) = (33971200:ℝ)/21425071 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84565073:ℝ)/21094400)-4 = (187473:ℝ)/21094400 by norm_num]
    exact paid_middle_370
  · change middlePayment 371 ≤ middleValue ((point 4 cut 1024 371+point 4 cut 1024 372)/2)
    have hp : middlePayment 371 = (640070478443:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 371+point 4 cut 1024 372)/2 = (84565579:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84565579:ℝ)/21094400) = (6794240:ℝ)/4284913 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84565579:ℝ)/21094400)-4 = (187979:ℝ)/21094400 by norm_num]
    exact paid_middle_371
  · change middlePayment 372 ≤ middleValue ((point 4 cut 1024 372+point 4 cut 1024 373)/2)
    have hp : middlePayment 372 = (640109921783:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 372+point 4 cut 1024 373)/2 = (16913217:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16913217:ℝ)/4218880) = (33971200:ℝ)/21424059 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16913217:ℝ)/4218880)-4 = (37697:ℝ)/4218880 by norm_num]
    exact paid_middle_372
  · change middlePayment 373 ≤ middleValue ((point 4 cut 1024 373+point 4 cut 1024 374)/2)
    have hp : middlePayment 373 = (640149366655:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 373+point 4 cut 1024 374)/2 = (84566591:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84566591:ℝ)/21094400) = (33971200:ℝ)/21423553 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84566591:ℝ)/21094400)-4 = (188991:ℝ)/21094400 by norm_num]
    exact paid_middle_373
  · change middlePayment 374 ≤ middleValue ((point 4 cut 1024 374+point 4 cut 1024 375)/2)
    have hp : middlePayment 374 = (640188813058:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 374+point 4 cut 1024 375)/2 = (84567097:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84567097:ℝ)/21094400) = (33971200:ℝ)/21423047 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84567097:ℝ)/21094400)-4 = (189497:ℝ)/21094400 by norm_num]
    exact paid_middle_374
  · change middlePayment 375 ≤ middleValue ((point 4 cut 1024 375+point 4 cut 1024 376)/2)
    have hp : middlePayment 375 = (640228260992:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 375+point 4 cut 1024 376)/2 = (84567603:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84567603:ℝ)/21094400) = (33971200:ℝ)/21422541 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84567603:ℝ)/21094400)-4 = (190003:ℝ)/21094400 by norm_num]
    exact paid_middle_375
  · change middlePayment 376 ≤ middleValue ((point 4 cut 1024 376+point 4 cut 1024 377)/2)
    have hp : middlePayment 376 = (640267710458:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 376+point 4 cut 1024 377)/2 = (84568109:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84568109:ℝ)/21094400) = (6794240:ℝ)/4284407 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84568109:ℝ)/21094400)-4 = (190509:ℝ)/21094400 by norm_num]
    exact paid_middle_376
  · change middlePayment 377 ≤ middleValue ((point 4 cut 1024 377+point 4 cut 1024 378)/2)
    have hp : middlePayment 377 = (640307161456:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 377+point 4 cut 1024 378)/2 = (16913723:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16913723:ℝ)/4218880) = (33971200:ℝ)/21421529 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16913723:ℝ)/4218880)-4 = (38203:ℝ)/4218880 by norm_num]
    exact paid_middle_377
  · change middlePayment 378 ≤ middleValue ((point 4 cut 1024 378+point 4 cut 1024 379)/2)
    have hp : middlePayment 378 = (640346613985:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 378+point 4 cut 1024 379)/2 = (84569121:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84569121:ℝ)/21094400) = (33971200:ℝ)/21421023 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84569121:ℝ)/21094400)-4 = (191521:ℝ)/21094400 by norm_num]
    exact paid_middle_378
  · change middlePayment 379 ≤ middleValue ((point 4 cut 1024 379+point 4 cut 1024 380)/2)
    have hp : middlePayment 379 = (640386068046:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 379+point 4 cut 1024 380)/2 = (84569627:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84569627:ℝ)/21094400) = (33971200:ℝ)/21420517 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84569627:ℝ)/21094400)-4 = (192027:ℝ)/21094400 by norm_num]
    exact paid_middle_379
  · change middlePayment 380 ≤ middleValue ((point 4 cut 1024 380+point 4 cut 1024 381)/2)
    have hp : middlePayment 380 = (640425523639:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 380+point 4 cut 1024 381)/2 = (84570133:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84570133:ℝ)/21094400) = (33971200:ℝ)/21420011 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84570133:ℝ)/21094400)-4 = (192533:ℝ)/21094400 by norm_num]
    exact paid_middle_380
  · change middlePayment 381 ≤ middleValue ((point 4 cut 1024 381+point 4 cut 1024 382)/2)
    have hp : middlePayment 381 = (640464980764:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 381+point 4 cut 1024 382)/2 = (84570639:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84570639:ℝ)/21094400) = (6794240:ℝ)/4283901 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84570639:ℝ)/21094400)-4 = (193039:ℝ)/21094400 by norm_num]
    exact paid_middle_381
  · change middlePayment 382 ≤ middleValue ((point 4 cut 1024 382+point 4 cut 1024 383)/2)
    have hp : middlePayment 382 = (640504439421:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 382+point 4 cut 1024 383)/2 = (16914229:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16914229:ℝ)/4218880) = (33971200:ℝ)/21418999 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16914229:ℝ)/4218880)-4 = (38709:ℝ)/4218880 by norm_num]
    exact paid_middle_382
  · change middlePayment 383 ≤ middleValue ((point 4 cut 1024 383+point 4 cut 1024 384)/2)
    have hp : middlePayment 383 = (640543899610:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 383+point 4 cut 1024 384)/2 = (84571651:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84571651:ℝ)/21094400) = (33971200:ℝ)/21418493 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84571651:ℝ)/21094400)-4 = (194051:ℝ)/21094400 by norm_num]
    exact paid_middle_383
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_023
