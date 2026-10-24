import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints001
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_001 (j : Fin 16) : middlePayment (16*1+j.val) ≤
    middleValue ((point 4 cut 1024 (16*1+j.val)+point 4 cut 1024 (16*1+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 16 ≤ middleValue ((point 4 cut 1024 16+point 4 cut 1024 17)/2)
    have hp : middlePayment 16 = (626164281189:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 16+point 4 cut 1024 17)/2 = (84385949:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84385949:ℝ)/21094400) = (6794240:ℝ)/4320839 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84385949:ℝ)/21094400)-4 = (8349:ℝ)/21094400 by norm_num]
    exact paid_middle_16
  · change middlePayment 17 ≤ middleValue ((point 4 cut 1024 17+point 4 cut 1024 18)/2)
    have hp : middlePayment 17 = (626203185738:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 17+point 4 cut 1024 18)/2 = (16877291:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16877291:ℝ)/4218880) = (33971200:ℝ)/21603689 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16877291:ℝ)/4218880)-4 = (1771:ℝ)/4218880 by norm_num]
    exact paid_middle_17
  · change middlePayment 18 ≤ middleValue ((point 4 cut 1024 18+point 4 cut 1024 19)/2)
    have hp : middlePayment 18 = (626242091792:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 18+point 4 cut 1024 19)/2 = (84386961:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84386961:ℝ)/21094400) = (33971200:ℝ)/21603183 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84386961:ℝ)/21094400)-4 = (9361:ℝ)/21094400 by norm_num]
    exact paid_middle_18
  · change middlePayment 19 ≤ middleValue ((point 4 cut 1024 19+point 4 cut 1024 20)/2)
    have hp : middlePayment 19 = (626280999350:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 19+point 4 cut 1024 20)/2 = (84387467:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84387467:ℝ)/21094400) = (33971200:ℝ)/21602677 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84387467:ℝ)/21094400)-4 = (9867:ℝ)/21094400 by norm_num]
    exact paid_middle_19
  · change middlePayment 20 ≤ middleValue ((point 4 cut 1024 20+point 4 cut 1024 21)/2)
    have hp : middlePayment 20 = (626319908412:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 20+point 4 cut 1024 21)/2 = (84387973:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84387973:ℝ)/21094400) = (33971200:ℝ)/21602171 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84387973:ℝ)/21094400)-4 = (10373:ℝ)/21094400 by norm_num]
    exact paid_middle_20
  · change middlePayment 21 ≤ middleValue ((point 4 cut 1024 21+point 4 cut 1024 22)/2)
    have hp : middlePayment 21 = (626358818979:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 21+point 4 cut 1024 22)/2 = (84388479:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84388479:ℝ)/21094400) = (6794240:ℝ)/4320333 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84388479:ℝ)/21094400)-4 = (10879:ℝ)/21094400 by norm_num]
    exact paid_middle_21
  · change middlePayment 22 ≤ middleValue ((point 4 cut 1024 22+point 4 cut 1024 23)/2)
    have hp : middlePayment 22 = (626397731051:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 22+point 4 cut 1024 23)/2 = (16877797:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16877797:ℝ)/4218880) = (33971200:ℝ)/21601159 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16877797:ℝ)/4218880)-4 = (2277:ℝ)/4218880 by norm_num]
    exact paid_middle_22
  · change middlePayment 23 ≤ middleValue ((point 4 cut 1024 23+point 4 cut 1024 24)/2)
    have hp : middlePayment 23 = (626436644627:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 23+point 4 cut 1024 24)/2 = (84389491:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84389491:ℝ)/21094400) = (33971200:ℝ)/21600653 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84389491:ℝ)/21094400)-4 = (11891:ℝ)/21094400 by norm_num]
    exact paid_middle_23
  · change middlePayment 24 ≤ middleValue ((point 4 cut 1024 24+point 4 cut 1024 25)/2)
    have hp : middlePayment 24 = (626475559709:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 24+point 4 cut 1024 25)/2 = (84389997:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84389997:ℝ)/21094400) = (33971200:ℝ)/21600147 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84389997:ℝ)/21094400)-4 = (12397:ℝ)/21094400 by norm_num]
    exact paid_middle_24
  · change middlePayment 25 ≤ middleValue ((point 4 cut 1024 25+point 4 cut 1024 26)/2)
    have hp : middlePayment 25 = (626514476294:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 25+point 4 cut 1024 26)/2 = (84390503:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84390503:ℝ)/21094400) = (33971200:ℝ)/21599641 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84390503:ℝ)/21094400)-4 = (12903:ℝ)/21094400 by norm_num]
    exact paid_middle_25
  · change middlePayment 26 ≤ middleValue ((point 4 cut 1024 26+point 4 cut 1024 27)/2)
    have hp : middlePayment 26 = (626553394385:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 26+point 4 cut 1024 27)/2 = (84391009:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84391009:ℝ)/21094400) = (6794240:ℝ)/4319827 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84391009:ℝ)/21094400)-4 = (13409:ℝ)/21094400 by norm_num]
    exact paid_middle_26
  · change middlePayment 27 ≤ middleValue ((point 4 cut 1024 27+point 4 cut 1024 28)/2)
    have hp : middlePayment 27 = (626592313981:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 27+point 4 cut 1024 28)/2 = (16878303:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16878303:ℝ)/4218880) = (33971200:ℝ)/21598629 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16878303:ℝ)/4218880)-4 = (2783:ℝ)/4218880 by norm_num]
    exact paid_middle_27
  · change middlePayment 28 ≤ middleValue ((point 4 cut 1024 28+point 4 cut 1024 29)/2)
    have hp : middlePayment 28 = (626631235082:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 28+point 4 cut 1024 29)/2 = (84392021:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84392021:ℝ)/21094400) = (33971200:ℝ)/21598123 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84392021:ℝ)/21094400)-4 = (14421:ℝ)/21094400 by norm_num]
    exact paid_middle_28
  · change middlePayment 29 ≤ middleValue ((point 4 cut 1024 29+point 4 cut 1024 30)/2)
    have hp : middlePayment 29 = (626670157688:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 29+point 4 cut 1024 30)/2 = (84392527:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84392527:ℝ)/21094400) = (33971200:ℝ)/21597617 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84392527:ℝ)/21094400)-4 = (14927:ℝ)/21094400 by norm_num]
    exact paid_middle_29
  · change middlePayment 30 ≤ middleValue ((point 4 cut 1024 30+point 4 cut 1024 31)/2)
    have hp : middlePayment 30 = (626709081799:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 30+point 4 cut 1024 31)/2 = (84393033:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84393033:ℝ)/21094400) = (33971200:ℝ)/21597111 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84393033:ℝ)/21094400)-4 = (15433:ℝ)/21094400 by norm_num]
    exact paid_middle_30
  · change middlePayment 31 ≤ middleValue ((point 4 cut 1024 31+point 4 cut 1024 32)/2)
    have hp : middlePayment 31 = (626748007416:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 31+point 4 cut 1024 32)/2 = (84393539:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84393539:ℝ)/21094400) = (6794240:ℝ)/4319321 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84393539:ℝ)/21094400)-4 = (15939:ℝ)/21094400 by norm_num]
    exact paid_middle_31
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_001
