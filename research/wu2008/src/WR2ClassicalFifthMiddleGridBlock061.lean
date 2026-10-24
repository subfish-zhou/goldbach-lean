import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints061
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_061 (j : Fin 16) : middlePayment (16*61+j.val) ≤
    middleValue ((point 4 cut 1024 (16*61+j.val)+point 4 cut 1024 (16*61+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 976 ≤ middleValue ((point 4 cut 1024 976+point 4 cut 1024 977)/2)
    have hp : middlePayment 976 = (664216351219:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 976+point 4 cut 1024 977)/2 = (84871709:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84871709:ℝ)/21094400) = (6794240:ℝ)/4223687 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84871709:ℝ)/21094400)-4 = (494109:ℝ)/21094400 by norm_num]
    exact paid_middle_976
  · change middlePayment 977 ≤ middleValue ((point 4 cut 1024 977+point 4 cut 1024 978)/2)
    have hp : middlePayment 977 = (664256735310:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 977+point 4 cut 1024 978)/2 = (16974443:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16974443:ℝ)/4218880) = (33971200:ℝ)/21117929 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16974443:ℝ)/4218880)-4 = (98923:ℝ)/4218880 by norm_num]
    exact paid_middle_977
  · change middlePayment 978 ≤ middleValue ((point 4 cut 1024 978+point 4 cut 1024 979)/2)
    have hp : middlePayment 978 = (664297120981:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 978+point 4 cut 1024 979)/2 = (824007:ℝ)/204800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((824007:ℝ)/204800) = (33971200:ℝ)/21117423 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((824007:ℝ)/204800)-4 = (4807:ℝ)/204800 by norm_num]
    exact paid_middle_978
  · change middlePayment 979 ≤ middleValue ((point 4 cut 1024 979+point 4 cut 1024 980)/2)
    have hp : middlePayment 979 = (664337508230:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 979+point 4 cut 1024 980)/2 = (84873227:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84873227:ℝ)/21094400) = (33971200:ℝ)/21116917 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84873227:ℝ)/21094400)-4 = (495627:ℝ)/21094400 by norm_num]
    exact paid_middle_979
  · change middlePayment 980 ≤ middleValue ((point 4 cut 1024 980+point 4 cut 1024 981)/2)
    have hp : middlePayment 980 = (664377897058:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 980+point 4 cut 1024 981)/2 = (84873733:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84873733:ℝ)/21094400) = (33971200:ℝ)/21116411 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84873733:ℝ)/21094400)-4 = (496133:ℝ)/21094400 by norm_num]
    exact paid_middle_980
  · change middlePayment 981 ≤ middleValue ((point 4 cut 1024 981+point 4 cut 1024 982)/2)
    have hp : middlePayment 981 = (664418287466:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 981+point 4 cut 1024 982)/2 = (84874239:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84874239:ℝ)/21094400) = (6794240:ℝ)/4223181 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84874239:ℝ)/21094400)-4 = (496639:ℝ)/21094400 by norm_num]
    exact paid_middle_981
  · change middlePayment 982 ≤ middleValue ((point 4 cut 1024 982+point 4 cut 1024 983)/2)
    have hp : middlePayment 982 = (664458679453:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 982+point 4 cut 1024 983)/2 = (16974949:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16974949:ℝ)/4218880) = (33971200:ℝ)/21115399 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16974949:ℝ)/4218880)-4 = (99429:ℝ)/4218880 by norm_num]
    exact paid_middle_982
  · change middlePayment 983 ≤ middleValue ((point 4 cut 1024 983+point 4 cut 1024 984)/2)
    have hp : middlePayment 983 = (664499073019:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 983+point 4 cut 1024 984)/2 = (84875251:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84875251:ℝ)/21094400) = (33971200:ℝ)/21114893 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84875251:ℝ)/21094400)-4 = (497651:ℝ)/21094400 by norm_num]
    exact paid_middle_983
  · change middlePayment 984 ≤ middleValue ((point 4 cut 1024 984+point 4 cut 1024 985)/2)
    have hp : middlePayment 984 = (664539468165:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 984+point 4 cut 1024 985)/2 = (84875757:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84875757:ℝ)/21094400) = (33971200:ℝ)/21114387 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84875757:ℝ)/21094400)-4 = (498157:ℝ)/21094400 by norm_num]
    exact paid_middle_984
  · change middlePayment 985 ≤ middleValue ((point 4 cut 1024 985+point 4 cut 1024 986)/2)
    have hp : middlePayment 985 = (664579864891:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 985+point 4 cut 1024 986)/2 = (84876263:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84876263:ℝ)/21094400) = (33971200:ℝ)/21113881 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84876263:ℝ)/21094400)-4 = (498663:ℝ)/21094400 by norm_num]
    exact paid_middle_985
  · change middlePayment 986 ≤ middleValue ((point 4 cut 1024 986+point 4 cut 1024 987)/2)
    have hp : middlePayment 986 = (664620263196:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 986+point 4 cut 1024 987)/2 = (84876769:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84876769:ℝ)/21094400) = (1358848:ℝ)/844535 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84876769:ℝ)/21094400)-4 = (499169:ℝ)/21094400 by norm_num]
    exact paid_middle_986
  · change middlePayment 987 ≤ middleValue ((point 4 cut 1024 987+point 4 cut 1024 988)/2)
    have hp : middlePayment 987 = (664660663081:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 987+point 4 cut 1024 988)/2 = (3395091:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3395091:ℝ)/843776) = (33971200:ℝ)/21112869 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3395091:ℝ)/843776)-4 = (19987:ℝ)/843776 by norm_num]
    exact paid_middle_987
  · change middlePayment 988 ≤ middleValue ((point 4 cut 1024 988+point 4 cut 1024 989)/2)
    have hp : middlePayment 988 = (664701064545:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 988+point 4 cut 1024 989)/2 = (84877781:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84877781:ℝ)/21094400) = (33971200:ℝ)/21112363 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84877781:ℝ)/21094400)-4 = (500181:ℝ)/21094400 by norm_num]
    exact paid_middle_988
  · change middlePayment 989 ≤ middleValue ((point 4 cut 1024 989+point 4 cut 1024 990)/2)
    have hp : middlePayment 989 = (664741467590:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 989+point 4 cut 1024 990)/2 = (84878287:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84878287:ℝ)/21094400) = (33971200:ℝ)/21111857 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84878287:ℝ)/21094400)-4 = (500687:ℝ)/21094400 by norm_num]
    exact paid_middle_989
  · change middlePayment 990 ≤ middleValue ((point 4 cut 1024 990+point 4 cut 1024 991)/2)
    have hp : middlePayment 990 = (664781872215:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 990+point 4 cut 1024 991)/2 = (84878793:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84878793:ℝ)/21094400) = (33971200:ℝ)/21111351 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84878793:ℝ)/21094400)-4 = (501193:ℝ)/21094400 by norm_num]
    exact paid_middle_990
  · change middlePayment 991 ≤ middleValue ((point 4 cut 1024 991+point 4 cut 1024 992)/2)
    have hp : middlePayment 991 = (664822278420:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 991+point 4 cut 1024 992)/2 = (84879299:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84879299:ℝ)/21094400) = (6794240:ℝ)/4222169 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84879299:ℝ)/21094400)-4 = (501699:ℝ)/21094400 by norm_num]
    exact paid_middle_991
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_061
