import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints048
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_048 (j : Fin 16) : middlePayment (16*48+j.val) ≤
    middleValue ((point 4 cut 1024 (16*48+j.val)+point 4 cut 1024 (16*48+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 768 ≤ middleValue ((point 4 cut 1024 768+point 4 cut 1024 769)/2)
    have hp : middlePayment 768 = (655850659805:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 768+point 4 cut 1024 769)/2 = (84766461:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84766461:ℝ)/21094400) = (33971200:ℝ)/21223683 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84766461:ℝ)/21094400)-4 = (388861:ℝ)/21094400 by norm_num]
    exact paid_middle_768
  · change middlePayment 769 ≤ middleValue ((point 4 cut 1024 769+point 4 cut 1024 770)/2)
    have hp : middlePayment 769 = (655890717202:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 769+point 4 cut 1024 770)/2 = (84766967:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84766967:ℝ)/21094400) = (33971200:ℝ)/21223177 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84766967:ℝ)/21094400)-4 = (389367:ℝ)/21094400 by norm_num]
    exact paid_middle_769
  · change middlePayment 770 ≤ middleValue ((point 4 cut 1024 770+point 4 cut 1024 771)/2)
    have hp : middlePayment 770 = (655930776161:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 770+point 4 cut 1024 771)/2 = (84767473:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84767473:ℝ)/21094400) = (33971200:ℝ)/21222671 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84767473:ℝ)/21094400)-4 = (389873:ℝ)/21094400 by norm_num]
    exact paid_middle_770
  · change middlePayment 771 ≤ middleValue ((point 4 cut 1024 771+point 4 cut 1024 772)/2)
    have hp : middlePayment 771 = (655970836683:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 771+point 4 cut 1024 772)/2 = (84767979:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84767979:ℝ)/21094400) = (6794240:ℝ)/4244433 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84767979:ℝ)/21094400)-4 = (390379:ℝ)/21094400 by norm_num]
    exact paid_middle_771
  · change middlePayment 772 ≤ middleValue ((point 4 cut 1024 772+point 4 cut 1024 773)/2)
    have hp : middlePayment 772 = (656010898767:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 772+point 4 cut 1024 773)/2 = (164599:ℝ)/40960 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164599:ℝ)/40960) = (33971200:ℝ)/21221659 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((164599:ℝ)/40960)-4 = (759:ℝ)/40960 by norm_num]
    exact paid_middle_772
  · change middlePayment 773 ≤ middleValue ((point 4 cut 1024 773+point 4 cut 1024 774)/2)
    have hp : middlePayment 773 = (656050962414:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 773+point 4 cut 1024 774)/2 = (84768991:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84768991:ℝ)/21094400) = (33971200:ℝ)/21221153 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84768991:ℝ)/21094400)-4 = (391391:ℝ)/21094400 by norm_num]
    exact paid_middle_773
  · change middlePayment 774 ≤ middleValue ((point 4 cut 1024 774+point 4 cut 1024 775)/2)
    have hp : middlePayment 774 = (656091027624:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 774+point 4 cut 1024 775)/2 = (84769497:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84769497:ℝ)/21094400) = (33971200:ℝ)/21220647 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84769497:ℝ)/21094400)-4 = (391897:ℝ)/21094400 by norm_num]
    exact paid_middle_774
  · change middlePayment 775 ≤ middleValue ((point 4 cut 1024 775+point 4 cut 1024 776)/2)
    have hp : middlePayment 775 = (656131094396:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 775+point 4 cut 1024 776)/2 = (84770003:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84770003:ℝ)/21094400) = (33971200:ℝ)/21220141 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84770003:ℝ)/21094400)-4 = (392403:ℝ)/21094400 by norm_num]
    exact paid_middle_775
  · change middlePayment 776 ≤ middleValue ((point 4 cut 1024 776+point 4 cut 1024 777)/2)
    have hp : middlePayment 776 = (656171162732:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 776+point 4 cut 1024 777)/2 = (84770509:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84770509:ℝ)/21094400) = (6794240:ℝ)/4243927 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84770509:ℝ)/21094400)-4 = (392909:ℝ)/21094400 by norm_num]
    exact paid_middle_776
  · change middlePayment 777 ≤ middleValue ((point 4 cut 1024 777+point 4 cut 1024 778)/2)
    have hp : middlePayment 777 = (656211232630:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 777+point 4 cut 1024 778)/2 = (16954203:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16954203:ℝ)/4218880) = (33971200:ℝ)/21219129 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16954203:ℝ)/4218880)-4 = (78683:ℝ)/4218880 by norm_num]
    exact paid_middle_777
  · change middlePayment 778 ≤ middleValue ((point 4 cut 1024 778+point 4 cut 1024 779)/2)
    have hp : middlePayment 778 = (656251304091:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 778+point 4 cut 1024 779)/2 = (84771521:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84771521:ℝ)/21094400) = (33971200:ℝ)/21218623 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84771521:ℝ)/21094400)-4 = (393921:ℝ)/21094400 by norm_num]
    exact paid_middle_778
  · change middlePayment 779 ≤ middleValue ((point 4 cut 1024 779+point 4 cut 1024 780)/2)
    have hp : middlePayment 779 = (656291377115:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 779+point 4 cut 1024 780)/2 = (84772027:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84772027:ℝ)/21094400) = (33971200:ℝ)/21218117 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84772027:ℝ)/21094400)-4 = (394427:ℝ)/21094400 by norm_num]
    exact paid_middle_779
  · change middlePayment 780 ≤ middleValue ((point 4 cut 1024 780+point 4 cut 1024 781)/2)
    have hp : middlePayment 780 = (656331451703:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 780+point 4 cut 1024 781)/2 = (84772533:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84772533:ℝ)/21094400) = (33971200:ℝ)/21217611 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84772533:ℝ)/21094400)-4 = (394933:ℝ)/21094400 by norm_num]
    exact paid_middle_780
  · change middlePayment 781 ≤ middleValue ((point 4 cut 1024 781+point 4 cut 1024 782)/2)
    have hp : middlePayment 781 = (656371527854:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 781+point 4 cut 1024 782)/2 = (84773039:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84773039:ℝ)/21094400) = (6794240:ℝ)/4243421 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84773039:ℝ)/21094400)-4 = (395439:ℝ)/21094400 by norm_num]
    exact paid_middle_781
  · change middlePayment 782 ≤ middleValue ((point 4 cut 1024 782+point 4 cut 1024 783)/2)
    have hp : middlePayment 782 = (656411605568:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 782+point 4 cut 1024 783)/2 = (16954709:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16954709:ℝ)/4218880) = (33971200:ℝ)/21216599 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16954709:ℝ)/4218880)-4 = (79189:ℝ)/4218880 by norm_num]
    exact paid_middle_782
  · change middlePayment 783 ≤ middleValue ((point 4 cut 1024 783+point 4 cut 1024 784)/2)
    have hp : middlePayment 783 = (656451684845:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 783+point 4 cut 1024 784)/2 = (84774051:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84774051:ℝ)/21094400) = (33971200:ℝ)/21216093 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84774051:ℝ)/21094400)-4 = (396451:ℝ)/21094400 by norm_num]
    exact paid_middle_783
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_048
