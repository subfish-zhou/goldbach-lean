import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints056
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_056 (j : Fin 16) : middlePayment (16*56+j.val) ≤
    middleValue ((point 4 cut 1024 (16*56+j.val)+point 4 cut 1024 (16*56+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 896 ≤ middleValue ((point 4 cut 1024 896+point 4 cut 1024 897)/2)
    have hp : middlePayment 896 = (660990732850:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 896+point 4 cut 1024 897)/2 = (84831229:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84831229:ℝ)/21094400) = (6794240:ℝ)/4231783 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84831229:ℝ)/21094400)-4 = (453629:ℝ)/21094400 by norm_num]
    exact paid_middle_896
  · change middlePayment 897 ≤ middleValue ((point 4 cut 1024 897+point 4 cut 1024 898)/2)
    have hp : middlePayment 897 = (661030990880:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 897+point 4 cut 1024 898)/2 = (16966347:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16966347:ℝ)/4218880) = (33971200:ℝ)/21158409 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16966347:ℝ)/4218880)-4 = (90827:ℝ)/4218880 by norm_num]
    exact paid_middle_897
  · change middlePayment 898 ≤ middleValue ((point 4 cut 1024 898+point 4 cut 1024 899)/2)
    have hp : middlePayment 898 = (661071250482:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 898+point 4 cut 1024 899)/2 = (84832241:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84832241:ℝ)/21094400) = (33971200:ℝ)/21157903 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84832241:ℝ)/21094400)-4 = (454641:ℝ)/21094400 by norm_num]
    exact paid_middle_898
  · change middlePayment 899 ≤ middleValue ((point 4 cut 1024 899+point 4 cut 1024 900)/2)
    have hp : middlePayment 899 = (661111511657:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 899+point 4 cut 1024 900)/2 = (84832747:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84832747:ℝ)/21094400) = (33971200:ℝ)/21157397 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84832747:ℝ)/21094400)-4 = (455147:ℝ)/21094400 by norm_num]
    exact paid_middle_899
  · change middlePayment 900 ≤ middleValue ((point 4 cut 1024 900+point 4 cut 1024 901)/2)
    have hp : middlePayment 900 = (661151774405:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 900+point 4 cut 1024 901)/2 = (84833253:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84833253:ℝ)/21094400) = (33971200:ℝ)/21156891 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84833253:ℝ)/21094400)-4 = (455653:ℝ)/21094400 by norm_num]
    exact paid_middle_900
  · change middlePayment 901 ≤ middleValue ((point 4 cut 1024 901+point 4 cut 1024 902)/2)
    have hp : middlePayment 901 = (661192038725:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 901+point 4 cut 1024 902)/2 = (84833759:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84833759:ℝ)/21094400) = (6794240:ℝ)/4231277 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84833759:ℝ)/21094400)-4 = (456159:ℝ)/21094400 by norm_num]
    exact paid_middle_901
  · change middlePayment 902 ≤ middleValue ((point 4 cut 1024 902+point 4 cut 1024 903)/2)
    have hp : middlePayment 902 = (661232304619:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 902+point 4 cut 1024 903)/2 = (16966853:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16966853:ℝ)/4218880) = (33971200:ℝ)/21155879 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16966853:ℝ)/4218880)-4 = (91333:ℝ)/4218880 by norm_num]
    exact paid_middle_902
  · change middlePayment 903 ≤ middleValue ((point 4 cut 1024 903+point 4 cut 1024 904)/2)
    have hp : middlePayment 903 = (661272572085:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 903+point 4 cut 1024 904)/2 = (84834771:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84834771:ℝ)/21094400) = (33971200:ℝ)/21155373 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84834771:ℝ)/21094400)-4 = (457171:ℝ)/21094400 by norm_num]
    exact paid_middle_903
  · change middlePayment 904 ≤ middleValue ((point 4 cut 1024 904+point 4 cut 1024 905)/2)
    have hp : middlePayment 904 = (661312841125:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 904+point 4 cut 1024 905)/2 = (84835277:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84835277:ℝ)/21094400) = (33971200:ℝ)/21154867 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84835277:ℝ)/21094400)-4 = (457677:ℝ)/21094400 by norm_num]
    exact paid_middle_904
  · change middlePayment 905 ≤ middleValue ((point 4 cut 1024 905+point 4 cut 1024 906)/2)
    have hp : middlePayment 905 = (661353111737:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 905+point 4 cut 1024 906)/2 = (84835783:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84835783:ℝ)/21094400) = (33971200:ℝ)/21154361 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84835783:ℝ)/21094400)-4 = (458183:ℝ)/21094400 by norm_num]
    exact paid_middle_905
  · change middlePayment 906 ≤ middleValue ((point 4 cut 1024 906+point 4 cut 1024 907)/2)
    have hp : middlePayment 906 = (661393383923:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 906+point 4 cut 1024 907)/2 = (84836289:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84836289:ℝ)/21094400) = (6794240:ℝ)/4230771 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84836289:ℝ)/21094400)-4 = (458689:ℝ)/21094400 by norm_num]
    exact paid_middle_906
  · change middlePayment 907 ≤ middleValue ((point 4 cut 1024 907+point 4 cut 1024 908)/2)
    have hp : middlePayment 907 = (661433657683:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 907+point 4 cut 1024 908)/2 = (16967359:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16967359:ℝ)/4218880) = (33971200:ℝ)/21153349 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16967359:ℝ)/4218880)-4 = (91839:ℝ)/4218880 by norm_num]
    exact paid_middle_907
  · change middlePayment 908 ≤ middleValue ((point 4 cut 1024 908+point 4 cut 1024 909)/2)
    have hp : middlePayment 908 = (661473933015:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 908+point 4 cut 1024 909)/2 = (84837301:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84837301:ℝ)/21094400) = (33971200:ℝ)/21152843 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84837301:ℝ)/21094400)-4 = (459701:ℝ)/21094400 by norm_num]
    exact paid_middle_908
  · change middlePayment 909 ≤ middleValue ((point 4 cut 1024 909+point 4 cut 1024 910)/2)
    have hp : middlePayment 909 = (661514209921:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 909+point 4 cut 1024 910)/2 = (84837807:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84837807:ℝ)/21094400) = (33971200:ℝ)/21152337 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84837807:ℝ)/21094400)-4 = (460207:ℝ)/21094400 by norm_num]
    exact paid_middle_909
  · change middlePayment 910 ≤ middleValue ((point 4 cut 1024 910+point 4 cut 1024 911)/2)
    have hp : middlePayment 910 = (661554488401:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 910+point 4 cut 1024 911)/2 = (84838313:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84838313:ℝ)/21094400) = (33971200:ℝ)/21151831 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84838313:ℝ)/21094400)-4 = (460713:ℝ)/21094400 by norm_num]
    exact paid_middle_910
  · change middlePayment 911 ≤ middleValue ((point 4 cut 1024 911+point 4 cut 1024 912)/2)
    have hp : middlePayment 911 = (661594768454:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 911+point 4 cut 1024 912)/2 = (84838819:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84838819:ℝ)/21094400) = (1358848:ℝ)/846053 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84838819:ℝ)/21094400)-4 = (461219:ℝ)/21094400 by norm_num]
    exact paid_middle_911
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_056
