import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints036
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_036 (j : Fin 16) : middlePayment (16*36+j.val) ≤
    middleValue ((point 4 cut 1024 (16*36+j.val)+point 4 cut 1024 (16*36+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 576 ≤ middleValue ((point 4 cut 1024 576+point 4 cut 1024 577)/2)
    have hp : middlePayment 576 = (648188492730:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 576+point 4 cut 1024 577)/2 = (84669309:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84669309:ℝ)/21094400) = (6794240:ℝ)/4264167 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84669309:ℝ)/21094400)-4 = (291709:ℝ)/21094400 by norm_num]
    exact paid_middle_576
  · change middlePayment 577 ≤ middleValue ((point 4 cut 1024 577+point 4 cut 1024 578)/2)
    have hp : middlePayment 577 = (648228251612:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 577+point 4 cut 1024 578)/2 = (16933963:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16933963:ℝ)/4218880) = (33971200:ℝ)/21320329 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16933963:ℝ)/4218880)-4 = (58443:ℝ)/4218880 by norm_num]
    exact paid_middle_577
  · change middlePayment 578 ≤ middleValue ((point 4 cut 1024 578+point 4 cut 1024 579)/2)
    have hp : middlePayment 578 = (648268012042:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 578+point 4 cut 1024 579)/2 = (84670321:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84670321:ℝ)/21094400) = (33971200:ℝ)/21319823 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84670321:ℝ)/21094400)-4 = (292721:ℝ)/21094400 by norm_num]
    exact paid_middle_578
  · change middlePayment 579 ≤ middleValue ((point 4 cut 1024 579+point 4 cut 1024 580)/2)
    have hp : middlePayment 579 = (648307774019:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 579+point 4 cut 1024 580)/2 = (84670827:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84670827:ℝ)/21094400) = (33971200:ℝ)/21319317 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84670827:ℝ)/21094400)-4 = (293227:ℝ)/21094400 by norm_num]
    exact paid_middle_579
  · change middlePayment 580 ≤ middleValue ((point 4 cut 1024 580+point 4 cut 1024 581)/2)
    have hp : middlePayment 580 = (648347537544:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 580+point 4 cut 1024 581)/2 = (84671333:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84671333:ℝ)/21094400) = (33971200:ℝ)/21318811 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84671333:ℝ)/21094400)-4 = (293733:ℝ)/21094400 by norm_num]
    exact paid_middle_580
  · change middlePayment 581 ≤ middleValue ((point 4 cut 1024 581+point 4 cut 1024 582)/2)
    have hp : middlePayment 581 = (648387302616:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 581+point 4 cut 1024 582)/2 = (84671839:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84671839:ℝ)/21094400) = (6794240:ℝ)/4263661 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84671839:ℝ)/21094400)-4 = (294239:ℝ)/21094400 by norm_num]
    exact paid_middle_581
  · change middlePayment 582 ≤ middleValue ((point 4 cut 1024 582+point 4 cut 1024 583)/2)
    have hp : middlePayment 582 = (648427069235:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 582+point 4 cut 1024 583)/2 = (16934469:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16934469:ℝ)/4218880) = (33971200:ℝ)/21317799 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16934469:ℝ)/4218880)-4 = (58949:ℝ)/4218880 by norm_num]
    exact paid_middle_582
  · change middlePayment 583 ≤ middleValue ((point 4 cut 1024 583+point 4 cut 1024 584)/2)
    have hp : middlePayment 583 = (648466837402:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 583+point 4 cut 1024 584)/2 = (84672851:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84672851:ℝ)/21094400) = (33971200:ℝ)/21317293 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84672851:ℝ)/21094400)-4 = (295251:ℝ)/21094400 by norm_num]
    exact paid_middle_583
  · change middlePayment 584 ≤ middleValue ((point 4 cut 1024 584+point 4 cut 1024 585)/2)
    have hp : middlePayment 584 = (648506607117:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 584+point 4 cut 1024 585)/2 = (84673357:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84673357:ℝ)/21094400) = (33971200:ℝ)/21316787 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84673357:ℝ)/21094400)-4 = (295757:ℝ)/21094400 by norm_num]
    exact paid_middle_584
  · change middlePayment 585 ≤ middleValue ((point 4 cut 1024 585+point 4 cut 1024 586)/2)
    have hp : middlePayment 585 = (648546378380:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 585+point 4 cut 1024 586)/2 = (84673863:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84673863:ℝ)/21094400) = (33971200:ℝ)/21316281 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84673863:ℝ)/21094400)-4 = (296263:ℝ)/21094400 by norm_num]
    exact paid_middle_585
  · change middlePayment 586 ≤ middleValue ((point 4 cut 1024 586+point 4 cut 1024 587)/2)
    have hp : middlePayment 586 = (648586151191:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 586+point 4 cut 1024 587)/2 = (84674369:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84674369:ℝ)/21094400) = (1358848:ℝ)/852631 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84674369:ℝ)/21094400)-4 = (296769:ℝ)/21094400 by norm_num]
    exact paid_middle_586
  · change middlePayment 587 ≤ middleValue ((point 4 cut 1024 587+point 4 cut 1024 588)/2)
    have hp : middlePayment 587 = (648625925549:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 587+point 4 cut 1024 588)/2 = (3386995:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3386995:ℝ)/843776) = (33971200:ℝ)/21315269 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3386995:ℝ)/843776)-4 = (11891:ℝ)/843776 by norm_num]
    exact paid_middle_587
  · change middlePayment 588 ≤ middleValue ((point 4 cut 1024 588+point 4 cut 1024 589)/2)
    have hp : middlePayment 588 = (648665701456:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 588+point 4 cut 1024 589)/2 = (84675381:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84675381:ℝ)/21094400) = (33971200:ℝ)/21314763 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84675381:ℝ)/21094400)-4 = (297781:ℝ)/21094400 by norm_num]
    exact paid_middle_588
  · change middlePayment 589 ≤ middleValue ((point 4 cut 1024 589+point 4 cut 1024 590)/2)
    have hp : middlePayment 589 = (648705478910:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 589+point 4 cut 1024 590)/2 = (84675887:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84675887:ℝ)/21094400) = (33971200:ℝ)/21314257 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84675887:ℝ)/21094400)-4 = (298287:ℝ)/21094400 by norm_num]
    exact paid_middle_589
  · change middlePayment 590 ≤ middleValue ((point 4 cut 1024 590+point 4 cut 1024 591)/2)
    have hp : middlePayment 590 = (648745257913:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 590+point 4 cut 1024 591)/2 = (84676393:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84676393:ℝ)/21094400) = (33971200:ℝ)/21313751 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84676393:ℝ)/21094400)-4 = (298793:ℝ)/21094400 by norm_num]
    exact paid_middle_590
  · change middlePayment 591 ≤ middleValue ((point 4 cut 1024 591+point 4 cut 1024 592)/2)
    have hp : middlePayment 591 = (648785038464:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 591+point 4 cut 1024 592)/2 = (84676899:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84676899:ℝ)/21094400) = (6794240:ℝ)/4262649 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84676899:ℝ)/21094400)-4 = (299299:ℝ)/21094400 by norm_num]
    exact paid_middle_591
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_036
