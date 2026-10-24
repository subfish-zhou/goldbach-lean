import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints059
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_059 (j : Fin 16) : middlePayment (16*59+j.val) ≤
    middleValue ((point 4 cut 1024 (16*59+j.val)+point 4 cut 1024 (16*59+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 944 ≤ middleValue ((point 4 cut 1024 944+point 4 cut 1024 945)/2)
    have hp : middlePayment 944 = (662924893549:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 944+point 4 cut 1024 945)/2 = (84855517:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84855517:ℝ)/21094400) = (33971200:ℝ)/21134627 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84855517:ℝ)/21094400)-4 = (477917:ℝ)/21094400 by norm_num]
    exact paid_middle_944
  · change middlePayment 945 ≤ middleValue ((point 4 cut 1024 945+point 4 cut 1024 946)/2)
    have hp : middlePayment 945 = (662965227154:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 945+point 4 cut 1024 946)/2 = (84856023:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84856023:ℝ)/21094400) = (33971200:ℝ)/21134121 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84856023:ℝ)/21094400)-4 = (478423:ℝ)/21094400 by norm_num]
    exact paid_middle_945
  · change middlePayment 946 ≤ middleValue ((point 4 cut 1024 946+point 4 cut 1024 947)/2)
    have hp : middlePayment 946 = (663005562335:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 946+point 4 cut 1024 947)/2 = (84856529:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84856529:ℝ)/21094400) = (6794240:ℝ)/4226723 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84856529:ℝ)/21094400)-4 = (478929:ℝ)/21094400 by norm_num]
    exact paid_middle_946
  · change middlePayment 947 ≤ middleValue ((point 4 cut 1024 947+point 4 cut 1024 948)/2)
    have hp : middlePayment 947 = (663045899093:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 947+point 4 cut 1024 948)/2 = (16971407:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16971407:ℝ)/4218880) = (33971200:ℝ)/21133109 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16971407:ℝ)/4218880)-4 = (95887:ℝ)/4218880 by norm_num]
    exact paid_middle_947
  · change middlePayment 948 ≤ middleValue ((point 4 cut 1024 948+point 4 cut 1024 949)/2)
    have hp : middlePayment 948 = (663086237427:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 948+point 4 cut 1024 949)/2 = (84857541:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84857541:ℝ)/21094400) = (33971200:ℝ)/21132603 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84857541:ℝ)/21094400)-4 = (479941:ℝ)/21094400 by norm_num]
    exact paid_middle_948
  · change middlePayment 949 ≤ middleValue ((point 4 cut 1024 949+point 4 cut 1024 950)/2)
    have hp : middlePayment 949 = (663126577338:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 949+point 4 cut 1024 950)/2 = (84858047:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84858047:ℝ)/21094400) = (33971200:ℝ)/21132097 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84858047:ℝ)/21094400)-4 = (480447:ℝ)/21094400 by norm_num]
    exact paid_middle_949
  · change middlePayment 950 ≤ middleValue ((point 4 cut 1024 950+point 4 cut 1024 951)/2)
    have hp : middlePayment 950 = (663166918826:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 950+point 4 cut 1024 951)/2 = (84858553:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84858553:ℝ)/21094400) = (33971200:ℝ)/21131591 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84858553:ℝ)/21094400)-4 = (480953:ℝ)/21094400 by norm_num]
    exact paid_middle_950
  · change middlePayment 951 ≤ middleValue ((point 4 cut 1024 951+point 4 cut 1024 952)/2)
    have hp : middlePayment 951 = (663207261891:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 951+point 4 cut 1024 952)/2 = (84859059:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84859059:ℝ)/21094400) = (6794240:ℝ)/4226217 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84859059:ℝ)/21094400)-4 = (481459:ℝ)/21094400 by norm_num]
    exact paid_middle_951
  · change middlePayment 952 ≤ middleValue ((point 4 cut 1024 952+point 4 cut 1024 953)/2)
    have hp : middlePayment 952 = (663247606532:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 952+point 4 cut 1024 953)/2 = (16971913:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16971913:ℝ)/4218880) = (33971200:ℝ)/21130579 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16971913:ℝ)/4218880)-4 = (96393:ℝ)/4218880 by norm_num]
    exact paid_middle_952
  · change middlePayment 953 ≤ middleValue ((point 4 cut 1024 953+point 4 cut 1024 954)/2)
    have hp : middlePayment 953 = (663287952751:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 953+point 4 cut 1024 954)/2 = (84860071:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84860071:ℝ)/21094400) = (33971200:ℝ)/21130073 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84860071:ℝ)/21094400)-4 = (482471:ℝ)/21094400 by norm_num]
    exact paid_middle_953
  · change middlePayment 954 ≤ middleValue ((point 4 cut 1024 954+point 4 cut 1024 955)/2)
    have hp : middlePayment 954 = (663328300547:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 954+point 4 cut 1024 955)/2 = (84860577:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84860577:ℝ)/21094400) = (33971200:ℝ)/21129567 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84860577:ℝ)/21094400)-4 = (482977:ℝ)/21094400 by norm_num]
    exact paid_middle_954
  · change middlePayment 955 ≤ middleValue ((point 4 cut 1024 955+point 4 cut 1024 956)/2)
    have hp : middlePayment 955 = (663368649920:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 955+point 4 cut 1024 956)/2 = (84861083:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84861083:ℝ)/21094400) = (33971200:ℝ)/21129061 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84861083:ℝ)/21094400)-4 = (483483:ℝ)/21094400 by norm_num]
    exact paid_middle_955
  · change middlePayment 956 ≤ middleValue ((point 4 cut 1024 956+point 4 cut 1024 957)/2)
    have hp : middlePayment 956 = (663409000870:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 956+point 4 cut 1024 957)/2 = (84861589:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84861589:ℝ)/21094400) = (6794240:ℝ)/4225711 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84861589:ℝ)/21094400)-4 = (483989:ℝ)/21094400 by norm_num]
    exact paid_middle_956
  · change middlePayment 957 ≤ middleValue ((point 4 cut 1024 957+point 4 cut 1024 958)/2)
    have hp : middlePayment 957 = (663449353397:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 957+point 4 cut 1024 958)/2 = (16972419:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16972419:ℝ)/4218880) = (33971200:ℝ)/21128049 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16972419:ℝ)/4218880)-4 = (96899:ℝ)/4218880 by norm_num]
    exact paid_middle_957
  · change middlePayment 958 ≤ middleValue ((point 4 cut 1024 958+point 4 cut 1024 959)/2)
    have hp : middlePayment 958 = (663489707502:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 958+point 4 cut 1024 959)/2 = (84862601:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84862601:ℝ)/21094400) = (33971200:ℝ)/21127543 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84862601:ℝ)/21094400)-4 = (485001:ℝ)/21094400 by norm_num]
    exact paid_middle_958
  · change middlePayment 959 ≤ middleValue ((point 4 cut 1024 959+point 4 cut 1024 960)/2)
    have hp : middlePayment 959 = (663530063184:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 959+point 4 cut 1024 960)/2 = (84863107:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84863107:ℝ)/21094400) = (33971200:ℝ)/21127037 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84863107:ℝ)/21094400)-4 = (485507:ℝ)/21094400 by norm_num]
    exact paid_middle_959
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_059
