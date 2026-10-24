import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints060
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_060 (j : Fin 16) : middlePayment (16*60+j.val) ≤
    middleValue ((point 4 cut 1024 (16*60+j.val)+point 4 cut 1024 (16*60+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 960 ≤ middleValue ((point 4 cut 1024 960+point 4 cut 1024 961)/2)
    have hp : middlePayment 960 = (663570420444:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 960+point 4 cut 1024 961)/2 = (84863613:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84863613:ℝ)/21094400) = (33971200:ℝ)/21126531 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84863613:ℝ)/21094400)-4 = (486013:ℝ)/21094400 by norm_num]
    exact paid_middle_960
  · change middlePayment 961 ≤ middleValue ((point 4 cut 1024 961+point 4 cut 1024 962)/2)
    have hp : middlePayment 961 = (663610779282:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 961+point 4 cut 1024 962)/2 = (84864119:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84864119:ℝ)/21094400) = (1358848:ℝ)/845041 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84864119:ℝ)/21094400)-4 = (486519:ℝ)/21094400 by norm_num]
    exact paid_middle_961
  · change middlePayment 962 ≤ middleValue ((point 4 cut 1024 962+point 4 cut 1024 963)/2)
    have hp : middlePayment 962 = (663651139697:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 962+point 4 cut 1024 963)/2 = (3394585:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3394585:ℝ)/843776) = (33971200:ℝ)/21125519 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3394585:ℝ)/843776)-4 = (19481:ℝ)/843776 by norm_num]
    exact paid_middle_962
  · change middlePayment 963 ≤ middleValue ((point 4 cut 1024 963+point 4 cut 1024 964)/2)
    have hp : middlePayment 963 = (663691501690:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 963+point 4 cut 1024 964)/2 = (84865131:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84865131:ℝ)/21094400) = (33971200:ℝ)/21125013 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84865131:ℝ)/21094400)-4 = (487531:ℝ)/21094400 by norm_num]
    exact paid_middle_963
  · change middlePayment 964 ≤ middleValue ((point 4 cut 1024 964+point 4 cut 1024 965)/2)
    have hp : middlePayment 964 = (663731865261:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 964+point 4 cut 1024 965)/2 = (84865637:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84865637:ℝ)/21094400) = (33971200:ℝ)/21124507 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84865637:ℝ)/21094400)-4 = (488037:ℝ)/21094400 by norm_num]
    exact paid_middle_964
  · change middlePayment 965 ≤ middleValue ((point 4 cut 1024 965+point 4 cut 1024 966)/2)
    have hp : middlePayment 965 = (663772230410:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 965+point 4 cut 1024 966)/2 = (84866143:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84866143:ℝ)/21094400) = (33971200:ℝ)/21124001 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84866143:ℝ)/21094400)-4 = (488543:ℝ)/21094400 by norm_num]
    exact paid_middle_965
  · change middlePayment 966 ≤ middleValue ((point 4 cut 1024 966+point 4 cut 1024 967)/2)
    have hp : middlePayment 966 = (663812597138:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 966+point 4 cut 1024 967)/2 = (84866649:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84866649:ℝ)/21094400) = (6794240:ℝ)/4224699 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84866649:ℝ)/21094400)-4 = (489049:ℝ)/21094400 by norm_num]
    exact paid_middle_966
  · change middlePayment 967 ≤ middleValue ((point 4 cut 1024 967+point 4 cut 1024 968)/2)
    have hp : middlePayment 967 = (663852965443:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 967+point 4 cut 1024 968)/2 = (16973431:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16973431:ℝ)/4218880) = (33971200:ℝ)/21122989 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16973431:ℝ)/4218880)-4 = (97911:ℝ)/4218880 by norm_num]
    exact paid_middle_967
  · change middlePayment 968 ≤ middleValue ((point 4 cut 1024 968+point 4 cut 1024 969)/2)
    have hp : middlePayment 968 = (663893335326:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 968+point 4 cut 1024 969)/2 = (84867661:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84867661:ℝ)/21094400) = (33971200:ℝ)/21122483 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84867661:ℝ)/21094400)-4 = (490061:ℝ)/21094400 by norm_num]
    exact paid_middle_968
  · change middlePayment 969 ≤ middleValue ((point 4 cut 1024 969+point 4 cut 1024 970)/2)
    have hp : middlePayment 969 = (663933706788:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 969+point 4 cut 1024 970)/2 = (84868167:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84868167:ℝ)/21094400) = (33971200:ℝ)/21121977 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84868167:ℝ)/21094400)-4 = (490567:ℝ)/21094400 by norm_num]
    exact paid_middle_969
  · change middlePayment 970 ≤ middleValue ((point 4 cut 1024 970+point 4 cut 1024 971)/2)
    have hp : middlePayment 970 = (663974079828:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 970+point 4 cut 1024 971)/2 = (84868673:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84868673:ℝ)/21094400) = (33971200:ℝ)/21121471 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84868673:ℝ)/21094400)-4 = (491073:ℝ)/21094400 by norm_num]
    exact paid_middle_970
  · change middlePayment 971 ≤ middleValue ((point 4 cut 1024 971+point 4 cut 1024 972)/2)
    have hp : middlePayment 971 = (664014454447:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 971+point 4 cut 1024 972)/2 = (84869179:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84869179:ℝ)/21094400) = (6794240:ℝ)/4224193 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84869179:ℝ)/21094400)-4 = (491579:ℝ)/21094400 by norm_num]
    exact paid_middle_971
  · change middlePayment 972 ≤ middleValue ((point 4 cut 1024 972+point 4 cut 1024 973)/2)
    have hp : middlePayment 972 = (664054830644:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 972+point 4 cut 1024 973)/2 = (16973937:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16973937:ℝ)/4218880) = (33971200:ℝ)/21120459 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16973937:ℝ)/4218880)-4 = (98417:ℝ)/4218880 by norm_num]
    exact paid_middle_972
  · change middlePayment 973 ≤ middleValue ((point 4 cut 1024 973+point 4 cut 1024 974)/2)
    have hp : middlePayment 973 = (664095208420:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 973+point 4 cut 1024 974)/2 = (84870191:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84870191:ℝ)/21094400) = (33971200:ℝ)/21119953 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84870191:ℝ)/21094400)-4 = (492591:ℝ)/21094400 by norm_num]
    exact paid_middle_973
  · change middlePayment 974 ≤ middleValue ((point 4 cut 1024 974+point 4 cut 1024 975)/2)
    have hp : middlePayment 974 = (664135587774:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 974+point 4 cut 1024 975)/2 = (84870697:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84870697:ℝ)/21094400) = (33971200:ℝ)/21119447 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84870697:ℝ)/21094400)-4 = (493097:ℝ)/21094400 by norm_num]
    exact paid_middle_974
  · change middlePayment 975 ≤ middleValue ((point 4 cut 1024 975+point 4 cut 1024 976)/2)
    have hp : middlePayment 975 = (664175968707:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 975+point 4 cut 1024 976)/2 = (84871203:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84871203:ℝ)/21094400) = (33971200:ℝ)/21118941 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84871203:ℝ)/21094400)-4 = (493603:ℝ)/21094400 by norm_num]
    exact paid_middle_975
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_060
