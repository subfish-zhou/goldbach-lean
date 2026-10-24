import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints047
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_047 (j : Fin 16) : middlePayment (16*47+j.val) ≤
    middleValue ((point 4 cut 1024 (16*47+j.val)+point 4 cut 1024 (16*47+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 752 ≤ middleValue ((point 4 cut 1024 752+point 4 cut 1024 753)/2)
    have hp : middlePayment 752 = (655209953875:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 752+point 4 cut 1024 753)/2 = (16951673:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16951673:ℝ)/4218880) = (33971200:ℝ)/21231779 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16951673:ℝ)/4218880)-4 = (76153:ℝ)/4218880 by norm_num]
    exact paid_middle_752
  · change middlePayment 753 ≤ middleValue ((point 4 cut 1024 753+point 4 cut 1024 754)/2)
    have hp : middlePayment 753 = (655249986284:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 753+point 4 cut 1024 754)/2 = (84758871:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84758871:ℝ)/21094400) = (33971200:ℝ)/21231273 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84758871:ℝ)/21094400)-4 = (381271:ℝ)/21094400 by norm_num]
    exact paid_middle_753
  · change middlePayment 754 ≤ middleValue ((point 4 cut 1024 754+point 4 cut 1024 755)/2)
    have hp : middlePayment 754 = (655290020255:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 754+point 4 cut 1024 755)/2 = (84759377:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84759377:ℝ)/21094400) = (33971200:ℝ)/21230767 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84759377:ℝ)/21094400)-4 = (381777:ℝ)/21094400 by norm_num]
    exact paid_middle_754
  · change middlePayment 755 ≤ middleValue ((point 4 cut 1024 755+point 4 cut 1024 756)/2)
    have hp : middlePayment 755 = (655330055787:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 755+point 4 cut 1024 756)/2 = (84759883:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84759883:ℝ)/21094400) = (33971200:ℝ)/21230261 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84759883:ℝ)/21094400)-4 = (382283:ℝ)/21094400 by norm_num]
    exact paid_middle_755
  · change middlePayment 756 ≤ middleValue ((point 4 cut 1024 756+point 4 cut 1024 757)/2)
    have hp : middlePayment 756 = (655370092880:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 756+point 4 cut 1024 757)/2 = (84760389:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84760389:ℝ)/21094400) = (6794240:ℝ)/4245951 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84760389:ℝ)/21094400)-4 = (382789:ℝ)/21094400 by norm_num]
    exact paid_middle_756
  · change middlePayment 757 ≤ middleValue ((point 4 cut 1024 757+point 4 cut 1024 758)/2)
    have hp : middlePayment 757 = (655410131534:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 757+point 4 cut 1024 758)/2 = (16952179:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16952179:ℝ)/4218880) = (33971200:ℝ)/21229249 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16952179:ℝ)/4218880)-4 = (76659:ℝ)/4218880 by norm_num]
    exact paid_middle_757
  · change middlePayment 758 ≤ middleValue ((point 4 cut 1024 758+point 4 cut 1024 759)/2)
    have hp : middlePayment 758 = (655450171750:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 758+point 4 cut 1024 759)/2 = (84761401:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84761401:ℝ)/21094400) = (33971200:ℝ)/21228743 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84761401:ℝ)/21094400)-4 = (383801:ℝ)/21094400 by norm_num]
    exact paid_middle_758
  · change middlePayment 759 ≤ middleValue ((point 4 cut 1024 759+point 4 cut 1024 760)/2)
    have hp : middlePayment 759 = (655490213527:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 759+point 4 cut 1024 760)/2 = (84761907:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84761907:ℝ)/21094400) = (33971200:ℝ)/21228237 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84761907:ℝ)/21094400)-4 = (384307:ℝ)/21094400 by norm_num]
    exact paid_middle_759
  · change middlePayment 760 ≤ middleValue ((point 4 cut 1024 760+point 4 cut 1024 761)/2)
    have hp : middlePayment 760 = (655530256866:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 760+point 4 cut 1024 761)/2 = (84762413:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84762413:ℝ)/21094400) = (33971200:ℝ)/21227731 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84762413:ℝ)/21094400)-4 = (384813:ℝ)/21094400 by norm_num]
    exact paid_middle_760
  · change middlePayment 761 ≤ middleValue ((point 4 cut 1024 761+point 4 cut 1024 762)/2)
    have hp : middlePayment 761 = (655570301767:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 761+point 4 cut 1024 762)/2 = (84762919:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84762919:ℝ)/21094400) = (1358848:ℝ)/849089 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84762919:ℝ)/21094400)-4 = (385319:ℝ)/21094400 by norm_num]
    exact paid_middle_761
  · change middlePayment 762 ≤ middleValue ((point 4 cut 1024 762+point 4 cut 1024 763)/2)
    have hp : middlePayment 762 = (655610348230:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 762+point 4 cut 1024 763)/2 = (3390537:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3390537:ℝ)/843776) = (33971200:ℝ)/21226719 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3390537:ℝ)/843776)-4 = (15433:ℝ)/843776 by norm_num]
    exact paid_middle_762
  · change middlePayment 763 ≤ middleValue ((point 4 cut 1024 763+point 4 cut 1024 764)/2)
    have hp : middlePayment 763 = (655650396254:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 763+point 4 cut 1024 764)/2 = (84763931:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84763931:ℝ)/21094400) = (33971200:ℝ)/21226213 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84763931:ℝ)/21094400)-4 = (386331:ℝ)/21094400 by norm_num]
    exact paid_middle_763
  · change middlePayment 764 ≤ middleValue ((point 4 cut 1024 764+point 4 cut 1024 765)/2)
    have hp : middlePayment 764 = (655690445840:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 764+point 4 cut 1024 765)/2 = (84764437:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84764437:ℝ)/21094400) = (33971200:ℝ)/21225707 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84764437:ℝ)/21094400)-4 = (386837:ℝ)/21094400 by norm_num]
    exact paid_middle_764
  · change middlePayment 765 ≤ middleValue ((point 4 cut 1024 765+point 4 cut 1024 766)/2)
    have hp : middlePayment 765 = (655730496988:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 765+point 4 cut 1024 766)/2 = (84764943:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84764943:ℝ)/21094400) = (33971200:ℝ)/21225201 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84764943:ℝ)/21094400)-4 = (387343:ℝ)/21094400 by norm_num]
    exact paid_middle_765
  · change middlePayment 766 ≤ middleValue ((point 4 cut 1024 766+point 4 cut 1024 767)/2)
    have hp : middlePayment 766 = (655770549698:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 766+point 4 cut 1024 767)/2 = (84765449:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84765449:ℝ)/21094400) = (6794240:ℝ)/4244939 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84765449:ℝ)/21094400)-4 = (387849:ℝ)/21094400 by norm_num]
    exact paid_middle_766
  · change middlePayment 767 ≤ middleValue ((point 4 cut 1024 767+point 4 cut 1024 768)/2)
    have hp : middlePayment 767 = (655810603971:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 767+point 4 cut 1024 768)/2 = (16953191:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16953191:ℝ)/4218880) = (33971200:ℝ)/21224189 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16953191:ℝ)/4218880)-4 = (77671:ℝ)/4218880 by norm_num]
    exact paid_middle_767
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_047
