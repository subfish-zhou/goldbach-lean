import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints052
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_052 (j : Fin 16) : middlePayment (16*52+j.val) ≤
    middleValue ((point 4 cut 1024 (16*52+j.val)+point 4 cut 1024 (16*52+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 832 ≤ middleValue ((point 4 cut 1024 832+point 4 cut 1024 833)/2)
    have hp : middlePayment 832 = (658417486289:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 832+point 4 cut 1024 833)/2 = (16959769:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16959769:ℝ)/4218880) = (33971200:ℝ)/21191299 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16959769:ℝ)/4218880)-4 = (84249:ℝ)/4218880 by norm_num]
    exact paid_middle_832
  · change middlePayment 833 ≤ middleValue ((point 4 cut 1024 833+point 4 cut 1024 834)/2)
    have hp : middlePayment 833 = (658457643839:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 833+point 4 cut 1024 834)/2 = (84799351:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84799351:ℝ)/21094400) = (33971200:ℝ)/21190793 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84799351:ℝ)/21094400)-4 = (421751:ℝ)/21094400 by norm_num]
    exact paid_middle_833
  · change middlePayment 834 ≤ middleValue ((point 4 cut 1024 834+point 4 cut 1024 835)/2)
    have hp : middlePayment 834 = (658497802957:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 834+point 4 cut 1024 835)/2 = (84799857:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84799857:ℝ)/21094400) = (33971200:ℝ)/21190287 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84799857:ℝ)/21094400)-4 = (422257:ℝ)/21094400 by norm_num]
    exact paid_middle_834
  · change middlePayment 835 ≤ middleValue ((point 4 cut 1024 835+point 4 cut 1024 836)/2)
    have hp : middlePayment 835 = (658537963642:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 835+point 4 cut 1024 836)/2 = (84800363:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84800363:ℝ)/21094400) = (33971200:ℝ)/21189781 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84800363:ℝ)/21094400)-4 = (422763:ℝ)/21094400 by norm_num]
    exact paid_middle_835
  · change middlePayment 836 ≤ middleValue ((point 4 cut 1024 836+point 4 cut 1024 837)/2)
    have hp : middlePayment 836 = (658578125894:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 836+point 4 cut 1024 837)/2 = (84800869:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84800869:ℝ)/21094400) = (1358848:ℝ)/847571 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84800869:ℝ)/21094400)-4 = (423269:ℝ)/21094400 by norm_num]
    exact paid_middle_836
  · change middlePayment 837 ≤ middleValue ((point 4 cut 1024 837+point 4 cut 1024 838)/2)
    have hp : middlePayment 837 = (658618289715:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 837+point 4 cut 1024 838)/2 = (3392055:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3392055:ℝ)/843776) = (33971200:ℝ)/21188769 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3392055:ℝ)/843776)-4 = (16951:ℝ)/843776 by norm_num]
    exact paid_middle_837
  · change middlePayment 838 ≤ middleValue ((point 4 cut 1024 838+point 4 cut 1024 839)/2)
    have hp : middlePayment 838 = (658658455103:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 838+point 4 cut 1024 839)/2 = (84801881:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84801881:ℝ)/21094400) = (33971200:ℝ)/21188263 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84801881:ℝ)/21094400)-4 = (424281:ℝ)/21094400 by norm_num]
    exact paid_middle_838
  · change middlePayment 839 ≤ middleValue ((point 4 cut 1024 839+point 4 cut 1024 840)/2)
    have hp : middlePayment 839 = (658698622059:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 839+point 4 cut 1024 840)/2 = (84802387:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84802387:ℝ)/21094400) = (33971200:ℝ)/21187757 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84802387:ℝ)/21094400)-4 = (424787:ℝ)/21094400 by norm_num]
    exact paid_middle_839
  · change middlePayment 840 ≤ middleValue ((point 4 cut 1024 840+point 4 cut 1024 841)/2)
    have hp : middlePayment 840 = (658738790583:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 840+point 4 cut 1024 841)/2 = (84802893:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84802893:ℝ)/21094400) = (33971200:ℝ)/21187251 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84802893:ℝ)/21094400)-4 = (425293:ℝ)/21094400 by norm_num]
    exact paid_middle_840
  · change middlePayment 841 ≤ middleValue ((point 4 cut 1024 841+point 4 cut 1024 842)/2)
    have hp : middlePayment 841 = (658778960675:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 841+point 4 cut 1024 842)/2 = (84803399:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84803399:ℝ)/21094400) = (6794240:ℝ)/4237349 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84803399:ℝ)/21094400)-4 = (425799:ℝ)/21094400 by norm_num]
    exact paid_middle_841
  · change middlePayment 842 ≤ middleValue ((point 4 cut 1024 842+point 4 cut 1024 843)/2)
    have hp : middlePayment 842 = (658819132335:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 842+point 4 cut 1024 843)/2 = (16960781:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16960781:ℝ)/4218880) = (33971200:ℝ)/21186239 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16960781:ℝ)/4218880)-4 = (85261:ℝ)/4218880 by norm_num]
    exact paid_middle_842
  · change middlePayment 843 ≤ middleValue ((point 4 cut 1024 843+point 4 cut 1024 844)/2)
    have hp : middlePayment 843 = (658859305563:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 843+point 4 cut 1024 844)/2 = (84804411:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84804411:ℝ)/21094400) = (33971200:ℝ)/21185733 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84804411:ℝ)/21094400)-4 = (426811:ℝ)/21094400 by norm_num]
    exact paid_middle_843
  · change middlePayment 844 ≤ middleValue ((point 4 cut 1024 844+point 4 cut 1024 845)/2)
    have hp : middlePayment 844 = (658899480360:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 844+point 4 cut 1024 845)/2 = (84804917:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84804917:ℝ)/21094400) = (33971200:ℝ)/21185227 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84804917:ℝ)/21094400)-4 = (427317:ℝ)/21094400 by norm_num]
    exact paid_middle_844
  · change middlePayment 845 ≤ middleValue ((point 4 cut 1024 845+point 4 cut 1024 846)/2)
    have hp : middlePayment 845 = (658939656725:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 845+point 4 cut 1024 846)/2 = (84805423:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84805423:ℝ)/21094400) = (33971200:ℝ)/21184721 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84805423:ℝ)/21094400)-4 = (427823:ℝ)/21094400 by norm_num]
    exact paid_middle_845
  · change middlePayment 846 ≤ middleValue ((point 4 cut 1024 846+point 4 cut 1024 847)/2)
    have hp : middlePayment 846 = (658979834658:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 846+point 4 cut 1024 847)/2 = (84805929:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84805929:ℝ)/21094400) = (6794240:ℝ)/4236843 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84805929:ℝ)/21094400)-4 = (428329:ℝ)/21094400 by norm_num]
    exact paid_middle_846
  · change middlePayment 847 ≤ middleValue ((point 4 cut 1024 847+point 4 cut 1024 848)/2)
    have hp : middlePayment 847 = (659020014160:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 847+point 4 cut 1024 848)/2 = (16961287:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16961287:ℝ)/4218880) = (33971200:ℝ)/21183709 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16961287:ℝ)/4218880)-4 = (85767:ℝ)/4218880 by norm_num]
    exact paid_middle_847
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_052
