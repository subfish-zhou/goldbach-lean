import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints049
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_049 (j : Fin 16) : middlePayment (16*49+j.val) ≤
    middleValue ((point 4 cut 1024 (16*49+j.val)+point 4 cut 1024 (16*49+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 784 ≤ middleValue ((point 4 cut 1024 784+point 4 cut 1024 785)/2)
    have hp : middlePayment 784 = (656491765686:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 784+point 4 cut 1024 785)/2 = (84774557:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84774557:ℝ)/21094400) = (33971200:ℝ)/21215587 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84774557:ℝ)/21094400)-4 = (396957:ℝ)/21094400 by norm_num]
    exact paid_middle_784
  · change middlePayment 785 ≤ middleValue ((point 4 cut 1024 785+point 4 cut 1024 786)/2)
    have hp : middlePayment 785 = (656531848091:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 785+point 4 cut 1024 786)/2 = (84775063:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84775063:ℝ)/21094400) = (33971200:ℝ)/21215081 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84775063:ℝ)/21094400)-4 = (397463:ℝ)/21094400 by norm_num]
    exact paid_middle_785
  · change middlePayment 786 ≤ middleValue ((point 4 cut 1024 786+point 4 cut 1024 787)/2)
    have hp : middlePayment 786 = (656571932059:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 786+point 4 cut 1024 787)/2 = (84775569:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84775569:ℝ)/21094400) = (1358848:ℝ)/848583 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84775569:ℝ)/21094400)-4 = (397969:ℝ)/21094400 by norm_num]
    exact paid_middle_786
  · change middlePayment 787 ≤ middleValue ((point 4 cut 1024 787+point 4 cut 1024 788)/2)
    have hp : middlePayment 787 = (656612017591:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 787+point 4 cut 1024 788)/2 = (3391043:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3391043:ℝ)/843776) = (33971200:ℝ)/21214069 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3391043:ℝ)/843776)-4 = (15939:ℝ)/843776 by norm_num]
    exact paid_middle_787
  · change middlePayment 788 ≤ middleValue ((point 4 cut 1024 788+point 4 cut 1024 789)/2)
    have hp : middlePayment 788 = (656652104687:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 788+point 4 cut 1024 789)/2 = (84776581:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84776581:ℝ)/21094400) = (33971200:ℝ)/21213563 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84776581:ℝ)/21094400)-4 = (398981:ℝ)/21094400 by norm_num]
    exact paid_middle_788
  · change middlePayment 789 ≤ middleValue ((point 4 cut 1024 789+point 4 cut 1024 790)/2)
    have hp : middlePayment 789 = (656692193347:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 789+point 4 cut 1024 790)/2 = (84777087:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84777087:ℝ)/21094400) = (33971200:ℝ)/21213057 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84777087:ℝ)/21094400)-4 = (399487:ℝ)/21094400 by norm_num]
    exact paid_middle_789
  · change middlePayment 790 ≤ middleValue ((point 4 cut 1024 790+point 4 cut 1024 791)/2)
    have hp : middlePayment 790 = (656732283570:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 790+point 4 cut 1024 791)/2 = (84777593:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84777593:ℝ)/21094400) = (33971200:ℝ)/21212551 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84777593:ℝ)/21094400)-4 = (399993:ℝ)/21094400 by norm_num]
    exact paid_middle_790
  · change middlePayment 791 ≤ middleValue ((point 4 cut 1024 791+point 4 cut 1024 792)/2)
    have hp : middlePayment 791 = (656772375358:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 791+point 4 cut 1024 792)/2 = (84778099:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84778099:ℝ)/21094400) = (6794240:ℝ)/4242409 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84778099:ℝ)/21094400)-4 = (400499:ℝ)/21094400 by norm_num]
    exact paid_middle_791
  · change middlePayment 792 ≤ middleValue ((point 4 cut 1024 792+point 4 cut 1024 793)/2)
    have hp : middlePayment 792 = (656812468710:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 792+point 4 cut 1024 793)/2 = (16955721:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16955721:ℝ)/4218880) = (33971200:ℝ)/21211539 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16955721:ℝ)/4218880)-4 = (80201:ℝ)/4218880 by norm_num]
    exact paid_middle_792
  · change middlePayment 793 ≤ middleValue ((point 4 cut 1024 793+point 4 cut 1024 794)/2)
    have hp : middlePayment 793 = (656852563626:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 793+point 4 cut 1024 794)/2 = (84779111:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84779111:ℝ)/21094400) = (33971200:ℝ)/21211033 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84779111:ℝ)/21094400)-4 = (401511:ℝ)/21094400 by norm_num]
    exact paid_middle_793
  · change middlePayment 794 ≤ middleValue ((point 4 cut 1024 794+point 4 cut 1024 795)/2)
    have hp : middlePayment 794 = (656892660107:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 794+point 4 cut 1024 795)/2 = (84779617:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84779617:ℝ)/21094400) = (33971200:ℝ)/21210527 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84779617:ℝ)/21094400)-4 = (402017:ℝ)/21094400 by norm_num]
    exact paid_middle_794
  · change middlePayment 795 ≤ middleValue ((point 4 cut 1024 795+point 4 cut 1024 796)/2)
    have hp : middlePayment 795 = (656932758151:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 795+point 4 cut 1024 796)/2 = (84780123:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84780123:ℝ)/21094400) = (33971200:ℝ)/21210021 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84780123:ℝ)/21094400)-4 = (402523:ℝ)/21094400 by norm_num]
    exact paid_middle_795
  · change middlePayment 796 ≤ middleValue ((point 4 cut 1024 796+point 4 cut 1024 797)/2)
    have hp : middlePayment 796 = (656972857761:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 796+point 4 cut 1024 797)/2 = (84780629:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84780629:ℝ)/21094400) = (6794240:ℝ)/4241903 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84780629:ℝ)/21094400)-4 = (403029:ℝ)/21094400 by norm_num]
    exact paid_middle_796
  · change middlePayment 797 ≤ middleValue ((point 4 cut 1024 797+point 4 cut 1024 798)/2)
    have hp : middlePayment 797 = (657012958934:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 797+point 4 cut 1024 798)/2 = (16956227:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16956227:ℝ)/4218880) = (33971200:ℝ)/21209009 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16956227:ℝ)/4218880)-4 = (80707:ℝ)/4218880 by norm_num]
    exact paid_middle_797
  · change middlePayment 798 ≤ middleValue ((point 4 cut 1024 798+point 4 cut 1024 799)/2)
    have hp : middlePayment 798 = (657053061673:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 798+point 4 cut 1024 799)/2 = (84781641:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84781641:ℝ)/21094400) = (33971200:ℝ)/21208503 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84781641:ℝ)/21094400)-4 = (404041:ℝ)/21094400 by norm_num]
    exact paid_middle_798
  · change middlePayment 799 ≤ middleValue ((point 4 cut 1024 799+point 4 cut 1024 800)/2)
    have hp : middlePayment 799 = (657093165976:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 799+point 4 cut 1024 800)/2 = (84782147:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84782147:ℝ)/21094400) = (33971200:ℝ)/21207997 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84782147:ℝ)/21094400)-4 = (404547:ℝ)/21094400 by norm_num]
    exact paid_middle_799
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_049
