import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints062
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_062 (j : Fin 16) : middlePayment (16*62+j.val) ≤
    middleValue ((point 4 cut 1024 (16*62+j.val)+point 4 cut 1024 (16*62+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 992 ≤ middleValue ((point 4 cut 1024 992+point 4 cut 1024 993)/2)
    have hp : middlePayment 992 = (664862686204:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 992+point 4 cut 1024 993)/2 = (16975961:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16975961:ℝ)/4218880) = (33971200:ℝ)/21110339 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16975961:ℝ)/4218880)-4 = (100441:ℝ)/4218880 by norm_num]
    exact paid_middle_992
  · change middlePayment 993 ≤ middleValue ((point 4 cut 1024 993+point 4 cut 1024 994)/2)
    have hp : middlePayment 993 = (664903095570:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 993+point 4 cut 1024 994)/2 = (84880311:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84880311:ℝ)/21094400) = (33971200:ℝ)/21109833 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84880311:ℝ)/21094400)-4 = (502711:ℝ)/21094400 by norm_num]
    exact paid_middle_993
  · change middlePayment 994 ≤ middleValue ((point 4 cut 1024 994+point 4 cut 1024 995)/2)
    have hp : middlePayment 994 = (664943506515:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 994+point 4 cut 1024 995)/2 = (84880817:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84880817:ℝ)/21094400) = (33971200:ℝ)/21109327 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84880817:ℝ)/21094400)-4 = (503217:ℝ)/21094400 by norm_num]
    exact paid_middle_994
  · change middlePayment 995 ≤ middleValue ((point 4 cut 1024 995+point 4 cut 1024 996)/2)
    have hp : middlePayment 995 = (664983919041:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 995+point 4 cut 1024 996)/2 = (84881323:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84881323:ℝ)/21094400) = (33971200:ℝ)/21108821 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84881323:ℝ)/21094400)-4 = (503723:ℝ)/21094400 by norm_num]
    exact paid_middle_995
  · change middlePayment 996 ≤ middleValue ((point 4 cut 1024 996+point 4 cut 1024 997)/2)
    have hp : middlePayment 996 = (665024333147:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 996+point 4 cut 1024 997)/2 = (84881829:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84881829:ℝ)/21094400) = (6794240:ℝ)/4221663 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84881829:ℝ)/21094400)-4 = (504229:ℝ)/21094400 by norm_num]
    exact paid_middle_996
  · change middlePayment 997 ≤ middleValue ((point 4 cut 1024 997+point 4 cut 1024 998)/2)
    have hp : middlePayment 997 = (665064748834:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 997+point 4 cut 1024 998)/2 = (16976467:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16976467:ℝ)/4218880) = (33971200:ℝ)/21107809 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16976467:ℝ)/4218880)-4 = (100947:ℝ)/4218880 by norm_num]
    exact paid_middle_997
  · change middlePayment 998 ≤ middleValue ((point 4 cut 1024 998+point 4 cut 1024 999)/2)
    have hp : middlePayment 998 = (665105166102:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 998+point 4 cut 1024 999)/2 = (84882841:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84882841:ℝ)/21094400) = (33971200:ℝ)/21107303 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84882841:ℝ)/21094400)-4 = (505241:ℝ)/21094400 by norm_num]
    exact paid_middle_998
  · change middlePayment 999 ≤ middleValue ((point 4 cut 1024 999+point 4 cut 1024 1000)/2)
    have hp : middlePayment 999 = (665145584950:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 999+point 4 cut 1024 1000)/2 = (84883347:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84883347:ℝ)/21094400) = (33971200:ℝ)/21106797 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84883347:ℝ)/21094400)-4 = (505747:ℝ)/21094400 by norm_num]
    exact paid_middle_999
  · change middlePayment 1000 ≤ middleValue ((point 4 cut 1024 1000+point 4 cut 1024 1001)/2)
    have hp : middlePayment 1000 = (665186005379:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1000+point 4 cut 1024 1001)/2 = (84883853:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84883853:ℝ)/21094400) = (33971200:ℝ)/21106291 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84883853:ℝ)/21094400)-4 = (506253:ℝ)/21094400 by norm_num]
    exact paid_middle_1000
  · change middlePayment 1001 ≤ middleValue ((point 4 cut 1024 1001+point 4 cut 1024 1002)/2)
    have hp : middlePayment 1001 = (665226427389:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1001+point 4 cut 1024 1002)/2 = (84884359:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84884359:ℝ)/21094400) = (6794240:ℝ)/4221157 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84884359:ℝ)/21094400)-4 = (506759:ℝ)/21094400 by norm_num]
    exact paid_middle_1001
  · change middlePayment 1002 ≤ middleValue ((point 4 cut 1024 1002+point 4 cut 1024 1003)/2)
    have hp : middlePayment 1002 = (665266850980:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1002+point 4 cut 1024 1003)/2 = (16976973:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16976973:ℝ)/4218880) = (33971200:ℝ)/21105279 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16976973:ℝ)/4218880)-4 = (101453:ℝ)/4218880 by norm_num]
    exact paid_middle_1002
  · change middlePayment 1003 ≤ middleValue ((point 4 cut 1024 1003+point 4 cut 1024 1004)/2)
    have hp : middlePayment 1003 = (665307276152:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1003+point 4 cut 1024 1004)/2 = (84885371:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84885371:ℝ)/21094400) = (33971200:ℝ)/21104773 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84885371:ℝ)/21094400)-4 = (507771:ℝ)/21094400 by norm_num]
    exact paid_middle_1003
  · change middlePayment 1004 ≤ middleValue ((point 4 cut 1024 1004+point 4 cut 1024 1005)/2)
    have hp : middlePayment 1004 = (665347702905:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1004+point 4 cut 1024 1005)/2 = (84885877:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84885877:ℝ)/21094400) = (33971200:ℝ)/21104267 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84885877:ℝ)/21094400)-4 = (508277:ℝ)/21094400 by norm_num]
    exact paid_middle_1004
  · change middlePayment 1005 ≤ middleValue ((point 4 cut 1024 1005+point 4 cut 1024 1006)/2)
    have hp : middlePayment 1005 = (665388131239:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1005+point 4 cut 1024 1006)/2 = (84886383:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84886383:ℝ)/21094400) = (33971200:ℝ)/21103761 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84886383:ℝ)/21094400)-4 = (508783:ℝ)/21094400 by norm_num]
    exact paid_middle_1005
  · change middlePayment 1006 ≤ middleValue ((point 4 cut 1024 1006+point 4 cut 1024 1007)/2)
    have hp : middlePayment 1006 = (665428561155:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1006+point 4 cut 1024 1007)/2 = (84886889:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84886889:ℝ)/21094400) = (6794240:ℝ)/4220651 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84886889:ℝ)/21094400)-4 = (509289:ℝ)/21094400 by norm_num]
    exact paid_middle_1006
  · change middlePayment 1007 ≤ middleValue ((point 4 cut 1024 1007+point 4 cut 1024 1008)/2)
    have hp : middlePayment 1007 = (665468992652:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1007+point 4 cut 1024 1008)/2 = (16977479:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16977479:ℝ)/4218880) = (33971200:ℝ)/21102749 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16977479:ℝ)/4218880)-4 = (101959:ℝ)/4218880 by norm_num]
    exact paid_middle_1007
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_062
