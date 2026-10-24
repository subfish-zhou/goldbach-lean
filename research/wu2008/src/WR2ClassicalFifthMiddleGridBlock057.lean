import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints057
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_057 (j : Fin 16) : middlePayment (16*57+j.val) ≤
    middleValue ((point 4 cut 1024 (16*57+j.val)+point 4 cut 1024 (16*57+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 912 ≤ middleValue ((point 4 cut 1024 912+point 4 cut 1024 913)/2)
    have hp : middlePayment 912 = (661635050081:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 912+point 4 cut 1024 913)/2 = (3393573:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3393573:ℝ)/843776) = (33971200:ℝ)/21150819 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3393573:ℝ)/843776)-4 = (18469:ℝ)/843776 by norm_num]
    exact paid_middle_912
  · change middlePayment 913 ≤ middleValue ((point 4 cut 1024 913+point 4 cut 1024 914)/2)
    have hp : middlePayment 913 = (661675333282:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 913+point 4 cut 1024 914)/2 = (84839831:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84839831:ℝ)/21094400) = (33971200:ℝ)/21150313 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84839831:ℝ)/21094400)-4 = (462231:ℝ)/21094400 by norm_num]
    exact paid_middle_913
  · change middlePayment 914 ≤ middleValue ((point 4 cut 1024 914+point 4 cut 1024 915)/2)
    have hp : middlePayment 914 = (661715618057:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 914+point 4 cut 1024 915)/2 = (84840337:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84840337:ℝ)/21094400) = (33971200:ℝ)/21149807 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84840337:ℝ)/21094400)-4 = (462737:ℝ)/21094400 by norm_num]
    exact paid_middle_914
  · change middlePayment 915 ≤ middleValue ((point 4 cut 1024 915+point 4 cut 1024 916)/2)
    have hp : middlePayment 915 = (661755904405:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 915+point 4 cut 1024 916)/2 = (84840843:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84840843:ℝ)/21094400) = (33971200:ℝ)/21149301 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84840843:ℝ)/21094400)-4 = (463243:ℝ)/21094400 by norm_num]
    exact paid_middle_915
  · change middlePayment 916 ≤ middleValue ((point 4 cut 1024 916+point 4 cut 1024 917)/2)
    have hp : middlePayment 916 = (661796192328:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 916+point 4 cut 1024 917)/2 = (84841349:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84841349:ℝ)/21094400) = (6794240:ℝ)/4229759 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84841349:ℝ)/21094400)-4 = (463749:ℝ)/21094400 by norm_num]
    exact paid_middle_916
  · change middlePayment 917 ≤ middleValue ((point 4 cut 1024 917+point 4 cut 1024 918)/2)
    have hp : middlePayment 917 = (661836481825:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 917+point 4 cut 1024 918)/2 = (16968371:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16968371:ℝ)/4218880) = (33971200:ℝ)/21148289 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16968371:ℝ)/4218880)-4 = (92851:ℝ)/4218880 by norm_num]
    exact paid_middle_917
  · change middlePayment 918 ≤ middleValue ((point 4 cut 1024 918+point 4 cut 1024 919)/2)
    have hp : middlePayment 918 = (661876772896:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 918+point 4 cut 1024 919)/2 = (84842361:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84842361:ℝ)/21094400) = (33971200:ℝ)/21147783 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84842361:ℝ)/21094400)-4 = (464761:ℝ)/21094400 by norm_num]
    exact paid_middle_918
  · change middlePayment 919 ≤ middleValue ((point 4 cut 1024 919+point 4 cut 1024 920)/2)
    have hp : middlePayment 919 = (661917065541:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 919+point 4 cut 1024 920)/2 = (84842867:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84842867:ℝ)/21094400) = (33971200:ℝ)/21147277 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84842867:ℝ)/21094400)-4 = (465267:ℝ)/21094400 by norm_num]
    exact paid_middle_919
  · change middlePayment 920 ≤ middleValue ((point 4 cut 1024 920+point 4 cut 1024 921)/2)
    have hp : middlePayment 920 = (661957359761:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 920+point 4 cut 1024 921)/2 = (84843373:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84843373:ℝ)/21094400) = (33971200:ℝ)/21146771 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84843373:ℝ)/21094400)-4 = (465773:ℝ)/21094400 by norm_num]
    exact paid_middle_920
  · change middlePayment 921 ≤ middleValue ((point 4 cut 1024 921+point 4 cut 1024 922)/2)
    have hp : middlePayment 921 = (661997655555:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 921+point 4 cut 1024 922)/2 = (84843879:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84843879:ℝ)/21094400) = (6794240:ℝ)/4229253 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84843879:ℝ)/21094400)-4 = (466279:ℝ)/21094400 by norm_num]
    exact paid_middle_921
  · change middlePayment 922 ≤ middleValue ((point 4 cut 1024 922+point 4 cut 1024 923)/2)
    have hp : middlePayment 922 = (662037952924:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 922+point 4 cut 1024 923)/2 = (16968877:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16968877:ℝ)/4218880) = (33971200:ℝ)/21145759 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16968877:ℝ)/4218880)-4 = (93357:ℝ)/4218880 by norm_num]
    exact paid_middle_922
  · change middlePayment 923 ≤ middleValue ((point 4 cut 1024 923+point 4 cut 1024 924)/2)
    have hp : middlePayment 923 = (662078251867:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 923+point 4 cut 1024 924)/2 = (84844891:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84844891:ℝ)/21094400) = (33971200:ℝ)/21145253 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84844891:ℝ)/21094400)-4 = (467291:ℝ)/21094400 by norm_num]
    exact paid_middle_923
  · change middlePayment 924 ≤ middleValue ((point 4 cut 1024 924+point 4 cut 1024 925)/2)
    have hp : middlePayment 924 = (662118552385:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 924+point 4 cut 1024 925)/2 = (84845397:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84845397:ℝ)/21094400) = (33971200:ℝ)/21144747 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84845397:ℝ)/21094400)-4 = (467797:ℝ)/21094400 by norm_num]
    exact paid_middle_924
  · change middlePayment 925 ≤ middleValue ((point 4 cut 1024 925+point 4 cut 1024 926)/2)
    have hp : middlePayment 925 = (662158854477:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 925+point 4 cut 1024 926)/2 = (84845903:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84845903:ℝ)/21094400) = (33971200:ℝ)/21144241 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84845903:ℝ)/21094400)-4 = (468303:ℝ)/21094400 by norm_num]
    exact paid_middle_925
  · change middlePayment 926 ≤ middleValue ((point 4 cut 1024 926+point 4 cut 1024 927)/2)
    have hp : middlePayment 926 = (662199158145:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 926+point 4 cut 1024 927)/2 = (84846409:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84846409:ℝ)/21094400) = (6794240:ℝ)/4228747 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84846409:ℝ)/21094400)-4 = (468809:ℝ)/21094400 by norm_num]
    exact paid_middle_926
  · change middlePayment 927 ≤ middleValue ((point 4 cut 1024 927+point 4 cut 1024 928)/2)
    have hp : middlePayment 927 = (662239463387:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 927+point 4 cut 1024 928)/2 = (16969383:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16969383:ℝ)/4218880) = (33971200:ℝ)/21143229 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16969383:ℝ)/4218880)-4 = (93863:ℝ)/4218880 by norm_num]
    exact paid_middle_927
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_057
