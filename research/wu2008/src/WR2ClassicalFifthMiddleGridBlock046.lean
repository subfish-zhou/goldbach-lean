import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints046
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_046 (j : Fin 16) : middlePayment (16*46+j.val) ≤
    middleValue ((point 4 cut 1024 (16*46+j.val)+point 4 cut 1024 (16*46+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 736 ≤ middleValue ((point 4 cut 1024 736+point 4 cut 1024 737)/2)
    have hp : middlePayment 736 = (654569647570:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 736+point 4 cut 1024 737)/2 = (84750269:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84750269:ℝ)/21094400) = (1358848:ℝ)/849595 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84750269:ℝ)/21094400)-4 = (372669:ℝ)/21094400 by norm_num]
    exact paid_middle_736
  · change middlePayment 737 ≤ middleValue ((point 4 cut 1024 737+point 4 cut 1024 738)/2)
    have hp : middlePayment 737 = (654609655013:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 737+point 4 cut 1024 738)/2 = (3390031:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3390031:ℝ)/843776) = (33971200:ℝ)/21239369 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3390031:ℝ)/843776)-4 = (14927:ℝ)/843776 by norm_num]
    exact paid_middle_737
  · change middlePayment 738 ≤ middleValue ((point 4 cut 1024 738+point 4 cut 1024 739)/2)
    have hp : middlePayment 738 = (654649664015:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 738+point 4 cut 1024 739)/2 = (84751281:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84751281:ℝ)/21094400) = (33971200:ℝ)/21238863 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84751281:ℝ)/21094400)-4 = (373681:ℝ)/21094400 by norm_num]
    exact paid_middle_738
  · change middlePayment 739 ≤ middleValue ((point 4 cut 1024 739+point 4 cut 1024 740)/2)
    have hp : middlePayment 739 = (654689674577:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 739+point 4 cut 1024 740)/2 = (84751787:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84751787:ℝ)/21094400) = (33971200:ℝ)/21238357 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84751787:ℝ)/21094400)-4 = (374187:ℝ)/21094400 by norm_num]
    exact paid_middle_739
  · change middlePayment 740 ≤ middleValue ((point 4 cut 1024 740+point 4 cut 1024 741)/2)
    have hp : middlePayment 740 = (654729686699:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 740+point 4 cut 1024 741)/2 = (84752293:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84752293:ℝ)/21094400) = (33971200:ℝ)/21237851 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84752293:ℝ)/21094400)-4 = (374693:ℝ)/21094400 by norm_num]
    exact paid_middle_740
  · change middlePayment 741 ≤ middleValue ((point 4 cut 1024 741+point 4 cut 1024 742)/2)
    have hp : middlePayment 741 = (654769700381:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 741+point 4 cut 1024 742)/2 = (84752799:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84752799:ℝ)/21094400) = (6794240:ℝ)/4247469 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84752799:ℝ)/21094400)-4 = (375199:ℝ)/21094400 by norm_num]
    exact paid_middle_741
  · change middlePayment 742 ≤ middleValue ((point 4 cut 1024 742+point 4 cut 1024 743)/2)
    have hp : middlePayment 742 = (654809715624:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 742+point 4 cut 1024 743)/2 = (16950661:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16950661:ℝ)/4218880) = (33971200:ℝ)/21236839 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16950661:ℝ)/4218880)-4 = (75141:ℝ)/4218880 by norm_num]
    exact paid_middle_742
  · change middlePayment 743 ≤ middleValue ((point 4 cut 1024 743+point 4 cut 1024 744)/2)
    have hp : middlePayment 743 = (654849732427:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 743+point 4 cut 1024 744)/2 = (84753811:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84753811:ℝ)/21094400) = (33971200:ℝ)/21236333 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84753811:ℝ)/21094400)-4 = (376211:ℝ)/21094400 by norm_num]
    exact paid_middle_743
  · change middlePayment 744 ≤ middleValue ((point 4 cut 1024 744+point 4 cut 1024 745)/2)
    have hp : middlePayment 744 = (654889750790:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 744+point 4 cut 1024 745)/2 = (84754317:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84754317:ℝ)/21094400) = (33971200:ℝ)/21235827 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84754317:ℝ)/21094400)-4 = (376717:ℝ)/21094400 by norm_num]
    exact paid_middle_744
  · change middlePayment 745 ≤ middleValue ((point 4 cut 1024 745+point 4 cut 1024 746)/2)
    have hp : middlePayment 745 = (654929770713:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 745+point 4 cut 1024 746)/2 = (84754823:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84754823:ℝ)/21094400) = (33971200:ℝ)/21235321 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84754823:ℝ)/21094400)-4 = (377223:ℝ)/21094400 by norm_num]
    exact paid_middle_745
  · change middlePayment 746 ≤ middleValue ((point 4 cut 1024 746+point 4 cut 1024 747)/2)
    have hp : middlePayment 746 = (654969792197:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 746+point 4 cut 1024 747)/2 = (84755329:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84755329:ℝ)/21094400) = (6794240:ℝ)/4246963 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84755329:ℝ)/21094400)-4 = (377729:ℝ)/21094400 by norm_num]
    exact paid_middle_746
  · change middlePayment 747 ≤ middleValue ((point 4 cut 1024 747+point 4 cut 1024 748)/2)
    have hp : middlePayment 747 = (655009815241:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 747+point 4 cut 1024 748)/2 = (16951167:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16951167:ℝ)/4218880) = (33971200:ℝ)/21234309 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16951167:ℝ)/4218880)-4 = (75647:ℝ)/4218880 by norm_num]
    exact paid_middle_747
  · change middlePayment 748 ≤ middleValue ((point 4 cut 1024 748+point 4 cut 1024 749)/2)
    have hp : middlePayment 748 = (655049839846:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 748+point 4 cut 1024 749)/2 = (84756341:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84756341:ℝ)/21094400) = (33971200:ℝ)/21233803 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84756341:ℝ)/21094400)-4 = (378741:ℝ)/21094400 by norm_num]
    exact paid_middle_748
  · change middlePayment 749 ≤ middleValue ((point 4 cut 1024 749+point 4 cut 1024 750)/2)
    have hp : middlePayment 749 = (655089866012:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 749+point 4 cut 1024 750)/2 = (84756847:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84756847:ℝ)/21094400) = (33971200:ℝ)/21233297 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84756847:ℝ)/21094400)-4 = (379247:ℝ)/21094400 by norm_num]
    exact paid_middle_749
  · change middlePayment 750 ≤ middleValue ((point 4 cut 1024 750+point 4 cut 1024 751)/2)
    have hp : middlePayment 750 = (655129893739:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 750+point 4 cut 1024 751)/2 = (84757353:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84757353:ℝ)/21094400) = (33971200:ℝ)/21232791 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84757353:ℝ)/21094400)-4 = (379753:ℝ)/21094400 by norm_num]
    exact paid_middle_750
  · change middlePayment 751 ≤ middleValue ((point 4 cut 1024 751+point 4 cut 1024 752)/2)
    have hp : middlePayment 751 = (655169923026:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 751+point 4 cut 1024 752)/2 = (84757859:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84757859:ℝ)/21094400) = (6794240:ℝ)/4246457 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84757859:ℝ)/21094400)-4 = (380259:ℝ)/21094400 by norm_num]
    exact paid_middle_751
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_046
