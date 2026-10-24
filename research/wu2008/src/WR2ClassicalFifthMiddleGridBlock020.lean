import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints020
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_020 (j : Fin 16) : middlePayment (16*20+j.val) ≤
    middleValue ((point 4 cut 1024 (16*20+j.val)+point 4 cut 1024 (16*20+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 320 ≤ middleValue ((point 4 cut 1024 320+point 4 cut 1024 321)/2)
    have hp : middlePayment 320 = (638060896829:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 320+point 4 cut 1024 321)/2 = (84539773:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84539773:ℝ)/21094400) = (33971200:ℝ)/21450371 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84539773:ℝ)/21094400)-4 = (162173:ℝ)/21094400 by norm_num]
    exact paid_middle_320
  · change middlePayment 321 ≤ middleValue ((point 4 cut 1024 321+point 4 cut 1024 322)/2)
    have hp : middlePayment 321 = (638100262173:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 321+point 4 cut 1024 322)/2 = (84540279:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84540279:ℝ)/21094400) = (6794240:ℝ)/4289973 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84540279:ℝ)/21094400)-4 = (162679:ℝ)/21094400 by norm_num]
    exact paid_middle_321
  · change middlePayment 322 ≤ middleValue ((point 4 cut 1024 322+point 4 cut 1024 323)/2)
    have hp : middlePayment 322 = (638139629045:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 322+point 4 cut 1024 323)/2 = (16908157:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16908157:ℝ)/4218880) = (33971200:ℝ)/21449359 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16908157:ℝ)/4218880)-4 = (32637:ℝ)/4218880 by norm_num]
    exact paid_middle_322
  · change middlePayment 323 ≤ middleValue ((point 4 cut 1024 323+point 4 cut 1024 324)/2)
    have hp : middlePayment 323 = (638178997445:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 323+point 4 cut 1024 324)/2 = (84541291:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84541291:ℝ)/21094400) = (33971200:ℝ)/21448853 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84541291:ℝ)/21094400)-4 = (163691:ℝ)/21094400 by norm_num]
    exact paid_middle_323
  · change middlePayment 324 ≤ middleValue ((point 4 cut 1024 324+point 4 cut 1024 325)/2)
    have hp : middlePayment 324 = (638218367372:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 324+point 4 cut 1024 325)/2 = (84541797:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84541797:ℝ)/21094400) = (33971200:ℝ)/21448347 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84541797:ℝ)/21094400)-4 = (164197:ℝ)/21094400 by norm_num]
    exact paid_middle_324
  · change middlePayment 325 ≤ middleValue ((point 4 cut 1024 325+point 4 cut 1024 326)/2)
    have hp : middlePayment 325 = (638257738826:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 325+point 4 cut 1024 326)/2 = (84542303:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84542303:ℝ)/21094400) = (33971200:ℝ)/21447841 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84542303:ℝ)/21094400)-4 = (164703:ℝ)/21094400 by norm_num]
    exact paid_middle_325
  · change middlePayment 326 ≤ middleValue ((point 4 cut 1024 326+point 4 cut 1024 327)/2)
    have hp : middlePayment 326 = (638297111809:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 326+point 4 cut 1024 327)/2 = (84542809:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84542809:ℝ)/21094400) = (6794240:ℝ)/4289467 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84542809:ℝ)/21094400)-4 = (165209:ℝ)/21094400 by norm_num]
    exact paid_middle_326
  · change middlePayment 327 ≤ middleValue ((point 4 cut 1024 327+point 4 cut 1024 328)/2)
    have hp : middlePayment 327 = (638336486319:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 327+point 4 cut 1024 328)/2 = (16908663:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16908663:ℝ)/4218880) = (33971200:ℝ)/21446829 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16908663:ℝ)/4218880)-4 = (33143:ℝ)/4218880 by norm_num]
    exact paid_middle_327
  · change middlePayment 328 ≤ middleValue ((point 4 cut 1024 328+point 4 cut 1024 329)/2)
    have hp : middlePayment 328 = (638375862357:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 328+point 4 cut 1024 329)/2 = (84543821:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84543821:ℝ)/21094400) = (33971200:ℝ)/21446323 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84543821:ℝ)/21094400)-4 = (166221:ℝ)/21094400 by norm_num]
    exact paid_middle_328
  · change middlePayment 329 ≤ middleValue ((point 4 cut 1024 329+point 4 cut 1024 330)/2)
    have hp : middlePayment 329 = (638415239923:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 329+point 4 cut 1024 330)/2 = (84544327:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84544327:ℝ)/21094400) = (33971200:ℝ)/21445817 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84544327:ℝ)/21094400)-4 = (166727:ℝ)/21094400 by norm_num]
    exact paid_middle_329
  · change middlePayment 330 ≤ middleValue ((point 4 cut 1024 330+point 4 cut 1024 331)/2)
    have hp : middlePayment 330 = (638454619017:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 330+point 4 cut 1024 331)/2 = (84544833:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84544833:ℝ)/21094400) = (33971200:ℝ)/21445311 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84544833:ℝ)/21094400)-4 = (167233:ℝ)/21094400 by norm_num]
    exact paid_middle_330
  · change middlePayment 331 ≤ middleValue ((point 4 cut 1024 331+point 4 cut 1024 332)/2)
    have hp : middlePayment 331 = (638493999639:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 331+point 4 cut 1024 332)/2 = (84545339:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84545339:ℝ)/21094400) = (6794240:ℝ)/4288961 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84545339:ℝ)/21094400)-4 = (167739:ℝ)/21094400 by norm_num]
    exact paid_middle_331
  · change middlePayment 332 ≤ middleValue ((point 4 cut 1024 332+point 4 cut 1024 333)/2)
    have hp : middlePayment 332 = (638533381790:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 332+point 4 cut 1024 333)/2 = (16909169:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16909169:ℝ)/4218880) = (33971200:ℝ)/21444299 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16909169:ℝ)/4218880)-4 = (33649:ℝ)/4218880 by norm_num]
    exact paid_middle_332
  · change middlePayment 333 ≤ middleValue ((point 4 cut 1024 333+point 4 cut 1024 334)/2)
    have hp : middlePayment 333 = (638572765468:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 333+point 4 cut 1024 334)/2 = (84546351:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84546351:ℝ)/21094400) = (33971200:ℝ)/21443793 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84546351:ℝ)/21094400)-4 = (168751:ℝ)/21094400 by norm_num]
    exact paid_middle_333
  · change middlePayment 334 ≤ middleValue ((point 4 cut 1024 334+point 4 cut 1024 335)/2)
    have hp : middlePayment 334 = (638612150675:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 334+point 4 cut 1024 335)/2 = (84546857:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84546857:ℝ)/21094400) = (33971200:ℝ)/21443287 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84546857:ℝ)/21094400)-4 = (169257:ℝ)/21094400 by norm_num]
    exact paid_middle_334
  · change middlePayment 335 ≤ middleValue ((point 4 cut 1024 335+point 4 cut 1024 336)/2)
    have hp : middlePayment 335 = (638651537410:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 335+point 4 cut 1024 336)/2 = (84547363:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84547363:ℝ)/21094400) = (33971200:ℝ)/21442781 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84547363:ℝ)/21094400)-4 = (169763:ℝ)/21094400 by norm_num]
    exact paid_middle_335
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_020
