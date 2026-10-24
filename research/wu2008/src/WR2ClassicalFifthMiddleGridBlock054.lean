import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints054
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_054 (j : Fin 16) : middlePayment (16*54+j.val) ≤
    middleValue ((point 4 cut 1024 (16*54+j.val)+point 4 cut 1024 (16*54+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 864 ≤ middleValue ((point 4 cut 1024 864+point 4 cut 1024 865)/2)
    have hp : middlePayment 864 = (659703305753:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 864+point 4 cut 1024 865)/2 = (84815037:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84815037:ℝ)/21094400) = (33971200:ℝ)/21175107 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84815037:ℝ)/21094400)-4 = (437437:ℝ)/21094400 by norm_num]
    exact paid_middle_864
  · change middlePayment 865 ≤ middleValue ((point 4 cut 1024 865+point 4 cut 1024 866)/2)
    have hp : middlePayment 865 = (659743513502:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 865+point 4 cut 1024 866)/2 = (84815543:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84815543:ℝ)/21094400) = (33971200:ℝ)/21174601 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84815543:ℝ)/21094400)-4 = (437943:ℝ)/21094400 by norm_num]
    exact paid_middle_865
  · change middlePayment 866 ≤ middleValue ((point 4 cut 1024 866+point 4 cut 1024 867)/2)
    have hp : middlePayment 866 = (659783722821:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 866+point 4 cut 1024 867)/2 = (84816049:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84816049:ℝ)/21094400) = (6794240:ℝ)/4234819 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84816049:ℝ)/21094400)-4 = (438449:ℝ)/21094400 by norm_num]
    exact paid_middle_866
  · change middlePayment 867 ≤ middleValue ((point 4 cut 1024 867+point 4 cut 1024 868)/2)
    have hp : middlePayment 867 = (659823933710:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 867+point 4 cut 1024 868)/2 = (16963311:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16963311:ℝ)/4218880) = (33971200:ℝ)/21173589 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16963311:ℝ)/4218880)-4 = (87791:ℝ)/4218880 by norm_num]
    exact paid_middle_867
  · change middlePayment 868 ≤ middleValue ((point 4 cut 1024 868+point 4 cut 1024 869)/2)
    have hp : middlePayment 868 = (659864146169:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 868+point 4 cut 1024 869)/2 = (84817061:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84817061:ℝ)/21094400) = (33971200:ℝ)/21173083 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84817061:ℝ)/21094400)-4 = (439461:ℝ)/21094400 by norm_num]
    exact paid_middle_868
  · change middlePayment 869 ≤ middleValue ((point 4 cut 1024 869+point 4 cut 1024 870)/2)
    have hp : middlePayment 869 = (659904360198:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 869+point 4 cut 1024 870)/2 = (84817567:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84817567:ℝ)/21094400) = (33971200:ℝ)/21172577 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84817567:ℝ)/21094400)-4 = (439967:ℝ)/21094400 by norm_num]
    exact paid_middle_869
  · change middlePayment 870 ≤ middleValue ((point 4 cut 1024 870+point 4 cut 1024 871)/2)
    have hp : middlePayment 870 = (659944575798:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 870+point 4 cut 1024 871)/2 = (84818073:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84818073:ℝ)/21094400) = (33971200:ℝ)/21172071 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84818073:ℝ)/21094400)-4 = (440473:ℝ)/21094400 by norm_num]
    exact paid_middle_870
  · change middlePayment 871 ≤ middleValue ((point 4 cut 1024 871+point 4 cut 1024 872)/2)
    have hp : middlePayment 871 = (659984792968:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 871+point 4 cut 1024 872)/2 = (84818579:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84818579:ℝ)/21094400) = (6794240:ℝ)/4234313 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84818579:ℝ)/21094400)-4 = (440979:ℝ)/21094400 by norm_num]
    exact paid_middle_871
  · change middlePayment 872 ≤ middleValue ((point 4 cut 1024 872+point 4 cut 1024 873)/2)
    have hp : middlePayment 872 = (660025011709:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 872+point 4 cut 1024 873)/2 = (16963817:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16963817:ℝ)/4218880) = (33971200:ℝ)/21171059 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16963817:ℝ)/4218880)-4 = (88297:ℝ)/4218880 by norm_num]
    exact paid_middle_872
  · change middlePayment 873 ≤ middleValue ((point 4 cut 1024 873+point 4 cut 1024 874)/2)
    have hp : middlePayment 873 = (660065232021:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 873+point 4 cut 1024 874)/2 = (84819591:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84819591:ℝ)/21094400) = (33971200:ℝ)/21170553 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84819591:ℝ)/21094400)-4 = (441991:ℝ)/21094400 by norm_num]
    exact paid_middle_873
  · change middlePayment 874 ≤ middleValue ((point 4 cut 1024 874+point 4 cut 1024 875)/2)
    have hp : middlePayment 874 = (660105453903:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 874+point 4 cut 1024 875)/2 = (84820097:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84820097:ℝ)/21094400) = (33971200:ℝ)/21170047 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84820097:ℝ)/21094400)-4 = (442497:ℝ)/21094400 by norm_num]
    exact paid_middle_874
  · change middlePayment 875 ≤ middleValue ((point 4 cut 1024 875+point 4 cut 1024 876)/2)
    have hp : middlePayment 875 = (660145677355:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 875+point 4 cut 1024 876)/2 = (823501:ℝ)/204800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((823501:ℝ)/204800) = (33971200:ℝ)/21169541 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((823501:ℝ)/204800)-4 = (4301:ℝ)/204800 by norm_num]
    exact paid_middle_875
  · change middlePayment 876 ≤ middleValue ((point 4 cut 1024 876+point 4 cut 1024 877)/2)
    have hp : middlePayment 876 = (660185902379:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 876+point 4 cut 1024 877)/2 = (84821109:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84821109:ℝ)/21094400) = (6794240:ℝ)/4233807 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84821109:ℝ)/21094400)-4 = (443509:ℝ)/21094400 by norm_num]
    exact paid_middle_876
  · change middlePayment 877 ≤ middleValue ((point 4 cut 1024 877+point 4 cut 1024 878)/2)
    have hp : middlePayment 877 = (660226128974:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 877+point 4 cut 1024 878)/2 = (16964323:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16964323:ℝ)/4218880) = (33971200:ℝ)/21168529 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16964323:ℝ)/4218880)-4 = (88803:ℝ)/4218880 by norm_num]
    exact paid_middle_877
  · change middlePayment 878 ≤ middleValue ((point 4 cut 1024 878+point 4 cut 1024 879)/2)
    have hp : middlePayment 878 = (660266357139:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 878+point 4 cut 1024 879)/2 = (84822121:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84822121:ℝ)/21094400) = (33971200:ℝ)/21168023 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84822121:ℝ)/21094400)-4 = (444521:ℝ)/21094400 by norm_num]
    exact paid_middle_878
  · change middlePayment 879 ≤ middleValue ((point 4 cut 1024 879+point 4 cut 1024 880)/2)
    have hp : middlePayment 879 = (660306586876:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 879+point 4 cut 1024 880)/2 = (84822627:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84822627:ℝ)/21094400) = (33971200:ℝ)/21167517 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84822627:ℝ)/21094400)-4 = (445027:ℝ)/21094400 by norm_num]
    exact paid_middle_879
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_054
