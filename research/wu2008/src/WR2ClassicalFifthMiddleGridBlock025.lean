import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints025
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_025 (j : Fin 16) : middlePayment (16*25+j.val) ≤
    middleValue ((point 4 cut 1024 (16*25+j.val)+point 4 cut 1024 (16*25+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 400 ≤ middleValue ((point 4 cut 1024 400+point 4 cut 1024 401)/2)
    have hp : middlePayment 400 = (641214957309:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 400+point 4 cut 1024 401)/2 = (84580253:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84580253:ℝ)/21094400) = (33971200:ℝ)/21409891 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84580253:ℝ)/21094400)-4 = (202653:ℝ)/21094400 by norm_num]
    exact paid_middle_400
  · change middlePayment 401 ≤ middleValue ((point 4 cut 1024 401+point 4 cut 1024 402)/2)
    have hp : middlePayment 401 = (641254445089:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 401+point 4 cut 1024 402)/2 = (84580759:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84580759:ℝ)/21094400) = (6794240:ℝ)/4281877 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84580759:ℝ)/21094400)-4 = (203159:ℝ)/21094400 by norm_num]
    exact paid_middle_401
  · change middlePayment 402 ≤ middleValue ((point 4 cut 1024 402+point 4 cut 1024 403)/2)
    have hp : middlePayment 402 = (641293934403:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 402+point 4 cut 1024 403)/2 = (16916253:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16916253:ℝ)/4218880) = (33971200:ℝ)/21408879 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16916253:ℝ)/4218880)-4 = (40733:ℝ)/4218880 by norm_num]
    exact paid_middle_402
  · change middlePayment 403 ≤ middleValue ((point 4 cut 1024 403+point 4 cut 1024 404)/2)
    have hp : middlePayment 403 = (641333425250:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 403+point 4 cut 1024 404)/2 = (84581771:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84581771:ℝ)/21094400) = (33971200:ℝ)/21408373 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84581771:ℝ)/21094400)-4 = (204171:ℝ)/21094400 by norm_num]
    exact paid_middle_403
  · change middlePayment 404 ≤ middleValue ((point 4 cut 1024 404+point 4 cut 1024 405)/2)
    have hp : middlePayment 404 = (641372917631:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 404+point 4 cut 1024 405)/2 = (84582277:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84582277:ℝ)/21094400) = (33971200:ℝ)/21407867 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84582277:ℝ)/21094400)-4 = (204677:ℝ)/21094400 by norm_num]
    exact paid_middle_404
  · change middlePayment 405 ≤ middleValue ((point 4 cut 1024 405+point 4 cut 1024 406)/2)
    have hp : middlePayment 405 = (641412411545:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 405+point 4 cut 1024 406)/2 = (84582783:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84582783:ℝ)/21094400) = (33971200:ℝ)/21407361 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84582783:ℝ)/21094400)-4 = (205183:ℝ)/21094400 by norm_num]
    exact paid_middle_405
  · change middlePayment 406 ≤ middleValue ((point 4 cut 1024 406+point 4 cut 1024 407)/2)
    have hp : middlePayment 406 = (641451906994:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 406+point 4 cut 1024 407)/2 = (84583289:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84583289:ℝ)/21094400) = (6794240:ℝ)/4281371 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84583289:ℝ)/21094400)-4 = (205689:ℝ)/21094400 by norm_num]
    exact paid_middle_406
  · change middlePayment 407 ≤ middleValue ((point 4 cut 1024 407+point 4 cut 1024 408)/2)
    have hp : middlePayment 407 = (641491403977:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 407+point 4 cut 1024 408)/2 = (16916759:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16916759:ℝ)/4218880) = (33971200:ℝ)/21406349 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16916759:ℝ)/4218880)-4 = (41239:ℝ)/4218880 by norm_num]
    exact paid_middle_407
  · change middlePayment 408 ≤ middleValue ((point 4 cut 1024 408+point 4 cut 1024 409)/2)
    have hp : middlePayment 408 = (641530902493:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 408+point 4 cut 1024 409)/2 = (84584301:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84584301:ℝ)/21094400) = (33971200:ℝ)/21405843 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84584301:ℝ)/21094400)-4 = (206701:ℝ)/21094400 by norm_num]
    exact paid_middle_408
  · change middlePayment 409 ≤ middleValue ((point 4 cut 1024 409+point 4 cut 1024 410)/2)
    have hp : middlePayment 409 = (641570402544:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 409+point 4 cut 1024 410)/2 = (84584807:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84584807:ℝ)/21094400) = (33971200:ℝ)/21405337 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84584807:ℝ)/21094400)-4 = (207207:ℝ)/21094400 by norm_num]
    exact paid_middle_409
  · change middlePayment 410 ≤ middleValue ((point 4 cut 1024 410+point 4 cut 1024 411)/2)
    have hp : middlePayment 410 = (641609904129:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 410+point 4 cut 1024 411)/2 = (84585313:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84585313:ℝ)/21094400) = (33971200:ℝ)/21404831 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84585313:ℝ)/21094400)-4 = (207713:ℝ)/21094400 by norm_num]
    exact paid_middle_410
  · change middlePayment 411 ≤ middleValue ((point 4 cut 1024 411+point 4 cut 1024 412)/2)
    have hp : middlePayment 411 = (641649407248:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 411+point 4 cut 1024 412)/2 = (84585819:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84585819:ℝ)/21094400) = (1358848:ℝ)/856173 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84585819:ℝ)/21094400)-4 = (208219:ℝ)/21094400 by norm_num]
    exact paid_middle_411
  · change middlePayment 412 ≤ middleValue ((point 4 cut 1024 412+point 4 cut 1024 413)/2)
    have hp : middlePayment 412 = (641688911901:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 412+point 4 cut 1024 413)/2 = (3383453:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3383453:ℝ)/843776) = (33971200:ℝ)/21403819 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3383453:ℝ)/843776)-4 = (8349:ℝ)/843776 by norm_num]
    exact paid_middle_412
  · change middlePayment 413 ≤ middleValue ((point 4 cut 1024 413+point 4 cut 1024 414)/2)
    have hp : middlePayment 413 = (641728418089:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 413+point 4 cut 1024 414)/2 = (84586831:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84586831:ℝ)/21094400) = (33971200:ℝ)/21403313 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84586831:ℝ)/21094400)-4 = (209231:ℝ)/21094400 by norm_num]
    exact paid_middle_413
  · change middlePayment 414 ≤ middleValue ((point 4 cut 1024 414+point 4 cut 1024 415)/2)
    have hp : middlePayment 414 = (641767925812:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 414+point 4 cut 1024 415)/2 = (84587337:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84587337:ℝ)/21094400) = (33971200:ℝ)/21402807 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84587337:ℝ)/21094400)-4 = (209737:ℝ)/21094400 by norm_num]
    exact paid_middle_414
  · change middlePayment 415 ≤ middleValue ((point 4 cut 1024 415+point 4 cut 1024 416)/2)
    have hp : middlePayment 415 = (641807435069:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 415+point 4 cut 1024 416)/2 = (84587843:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84587843:ℝ)/21094400) = (33971200:ℝ)/21402301 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84587843:ℝ)/21094400)-4 = (210243:ℝ)/21094400 by norm_num]
    exact paid_middle_415
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_025
