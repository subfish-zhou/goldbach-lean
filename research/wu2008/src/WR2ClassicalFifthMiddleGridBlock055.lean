import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints055
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_055 (j : Fin 16) : middlePayment (16*55+j.val) ≤
    middleValue ((point 4 cut 1024 (16*55+j.val)+point 4 cut 1024 (16*55+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 880 ≤ middleValue ((point 4 cut 1024 880+point 4 cut 1024 881)/2)
    have hp : middlePayment 880 = (660346818184:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 880+point 4 cut 1024 881)/2 = (84823133:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84823133:ℝ)/21094400) = (33971200:ℝ)/21167011 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84823133:ℝ)/21094400)-4 = (445533:ℝ)/21094400 by norm_num]
    exact paid_middle_880
  · change middlePayment 881 ≤ middleValue ((point 4 cut 1024 881+point 4 cut 1024 882)/2)
    have hp : middlePayment 881 = (660387051063:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 881+point 4 cut 1024 882)/2 = (84823639:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84823639:ℝ)/21094400) = (6794240:ℝ)/4233301 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84823639:ℝ)/21094400)-4 = (446039:ℝ)/21094400 by norm_num]
    exact paid_middle_881
  · change middlePayment 882 ≤ middleValue ((point 4 cut 1024 882+point 4 cut 1024 883)/2)
    have hp : middlePayment 882 = (660427285513:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 882+point 4 cut 1024 883)/2 = (16964829:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16964829:ℝ)/4218880) = (33971200:ℝ)/21165999 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16964829:ℝ)/4218880)-4 = (89309:ℝ)/4218880 by norm_num]
    exact paid_middle_882
  · change middlePayment 883 ≤ middleValue ((point 4 cut 1024 883+point 4 cut 1024 884)/2)
    have hp : middlePayment 883 = (660467521535:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 883+point 4 cut 1024 884)/2 = (84824651:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84824651:ℝ)/21094400) = (33971200:ℝ)/21165493 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84824651:ℝ)/21094400)-4 = (447051:ℝ)/21094400 by norm_num]
    exact paid_middle_883
  · change middlePayment 884 ≤ middleValue ((point 4 cut 1024 884+point 4 cut 1024 885)/2)
    have hp : middlePayment 884 = (660507759128:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 884+point 4 cut 1024 885)/2 = (84825157:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84825157:ℝ)/21094400) = (33971200:ℝ)/21164987 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84825157:ℝ)/21094400)-4 = (447557:ℝ)/21094400 by norm_num]
    exact paid_middle_884
  · change middlePayment 885 ≤ middleValue ((point 4 cut 1024 885+point 4 cut 1024 886)/2)
    have hp : middlePayment 885 = (660547998293:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 885+point 4 cut 1024 886)/2 = (84825663:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84825663:ℝ)/21094400) = (33971200:ℝ)/21164481 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84825663:ℝ)/21094400)-4 = (448063:ℝ)/21094400 by norm_num]
    exact paid_middle_885
  · change middlePayment 886 ≤ middleValue ((point 4 cut 1024 886+point 4 cut 1024 887)/2)
    have hp : middlePayment 886 = (660588239029:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 886+point 4 cut 1024 887)/2 = (84826169:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84826169:ℝ)/21094400) = (1358848:ℝ)/846559 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84826169:ℝ)/21094400)-4 = (448569:ℝ)/21094400 by norm_num]
    exact paid_middle_886
  · change middlePayment 887 ≤ middleValue ((point 4 cut 1024 887+point 4 cut 1024 888)/2)
    have hp : middlePayment 887 = (660628481337:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 887+point 4 cut 1024 888)/2 = (3393067:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3393067:ℝ)/843776) = (33971200:ℝ)/21163469 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3393067:ℝ)/843776)-4 = (17963:ℝ)/843776 by norm_num]
    exact paid_middle_887
  · change middlePayment 888 ≤ middleValue ((point 4 cut 1024 888+point 4 cut 1024 889)/2)
    have hp : middlePayment 888 = (660668725217:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 888+point 4 cut 1024 889)/2 = (84827181:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84827181:ℝ)/21094400) = (33971200:ℝ)/21162963 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84827181:ℝ)/21094400)-4 = (449581:ℝ)/21094400 by norm_num]
    exact paid_middle_888
  · change middlePayment 889 ≤ middleValue ((point 4 cut 1024 889+point 4 cut 1024 890)/2)
    have hp : middlePayment 889 = (660708970669:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 889+point 4 cut 1024 890)/2 = (84827687:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84827687:ℝ)/21094400) = (33971200:ℝ)/21162457 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84827687:ℝ)/21094400)-4 = (450087:ℝ)/21094400 by norm_num]
    exact paid_middle_889
  · change middlePayment 890 ≤ middleValue ((point 4 cut 1024 890+point 4 cut 1024 891)/2)
    have hp : middlePayment 890 = (660749217692:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 890+point 4 cut 1024 891)/2 = (84828193:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84828193:ℝ)/21094400) = (33971200:ℝ)/21161951 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84828193:ℝ)/21094400)-4 = (450593:ℝ)/21094400 by norm_num]
    exact paid_middle_890
  · change middlePayment 891 ≤ middleValue ((point 4 cut 1024 891+point 4 cut 1024 892)/2)
    have hp : middlePayment 891 = (660789466288:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 891+point 4 cut 1024 892)/2 = (84828699:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84828699:ℝ)/21094400) = (6794240:ℝ)/4232289 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84828699:ℝ)/21094400)-4 = (451099:ℝ)/21094400 by norm_num]
    exact paid_middle_891
  · change middlePayment 892 ≤ middleValue ((point 4 cut 1024 892+point 4 cut 1024 893)/2)
    have hp : middlePayment 892 = (660829716456:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 892+point 4 cut 1024 893)/2 = (16965841:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16965841:ℝ)/4218880) = (33971200:ℝ)/21160939 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16965841:ℝ)/4218880)-4 = (90321:ℝ)/4218880 by norm_num]
    exact paid_middle_892
  · change middlePayment 893 ≤ middleValue ((point 4 cut 1024 893+point 4 cut 1024 894)/2)
    have hp : middlePayment 893 = (660869968196:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 893+point 4 cut 1024 894)/2 = (84829711:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84829711:ℝ)/21094400) = (33971200:ℝ)/21160433 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84829711:ℝ)/21094400)-4 = (452111:ℝ)/21094400 by norm_num]
    exact paid_middle_893
  · change middlePayment 894 ≤ middleValue ((point 4 cut 1024 894+point 4 cut 1024 895)/2)
    have hp : middlePayment 894 = (660910221509:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 894+point 4 cut 1024 895)/2 = (84830217:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84830217:ℝ)/21094400) = (33971200:ℝ)/21159927 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84830217:ℝ)/21094400)-4 = (452617:ℝ)/21094400 by norm_num]
    exact paid_middle_894
  · change middlePayment 895 ≤ middleValue ((point 4 cut 1024 895+point 4 cut 1024 896)/2)
    have hp : middlePayment 895 = (660950476393:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 895+point 4 cut 1024 896)/2 = (84830723:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84830723:ℝ)/21094400) = (33971200:ℝ)/21159421 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84830723:ℝ)/21094400)-4 = (453123:ℝ)/21094400 by norm_num]
    exact paid_middle_895
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_055
