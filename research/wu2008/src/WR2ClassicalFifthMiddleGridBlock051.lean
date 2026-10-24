import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints051
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_051 (j : Fin 16) : middlePayment (16*51+j.val) ≤
    middleValue ((point 4 cut 1024 (16*51+j.val)+point 4 cut 1024 (16*51+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 816 ≤ middleValue ((point 4 cut 1024 816+point 4 cut 1024 817)/2)
    have hp : middlePayment 816 = (657775178602:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 816+point 4 cut 1024 817)/2 = (84790749:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84790749:ℝ)/21094400) = (6794240:ℝ)/4239879 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84790749:ℝ)/21094400)-4 = (413149:ℝ)/21094400 by norm_num]
    exact paid_middle_816
  · change middlePayment 817 ≤ middleValue ((point 4 cut 1024 817+point 4 cut 1024 818)/2)
    have hp : middlePayment 817 = (657815311084:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 817+point 4 cut 1024 818)/2 = (16958251:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16958251:ℝ)/4218880) = (33971200:ℝ)/21198889 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16958251:ℝ)/4218880)-4 = (82731:ℝ)/4218880 by norm_num]
    exact paid_middle_817
  · change middlePayment 818 ≤ middleValue ((point 4 cut 1024 818+point 4 cut 1024 819)/2)
    have hp : middlePayment 818 = (657855445131:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 818+point 4 cut 1024 819)/2 = (84791761:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84791761:ℝ)/21094400) = (33971200:ℝ)/21198383 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84791761:ℝ)/21094400)-4 = (414161:ℝ)/21094400 by norm_num]
    exact paid_middle_818
  · change middlePayment 819 ≤ middleValue ((point 4 cut 1024 819+point 4 cut 1024 820)/2)
    have hp : middlePayment 819 = (657895580745:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 819+point 4 cut 1024 820)/2 = (84792267:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84792267:ℝ)/21094400) = (33971200:ℝ)/21197877 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84792267:ℝ)/21094400)-4 = (414667:ℝ)/21094400 by norm_num]
    exact paid_middle_819
  · change middlePayment 820 ≤ middleValue ((point 4 cut 1024 820+point 4 cut 1024 821)/2)
    have hp : middlePayment 820 = (657935717924:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 820+point 4 cut 1024 821)/2 = (84792773:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84792773:ℝ)/21094400) = (33971200:ℝ)/21197371 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84792773:ℝ)/21094400)-4 = (415173:ℝ)/21094400 by norm_num]
    exact paid_middle_820
  · change middlePayment 821 ≤ middleValue ((point 4 cut 1024 821+point 4 cut 1024 822)/2)
    have hp : middlePayment 821 = (657975856671:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 821+point 4 cut 1024 822)/2 = (84793279:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84793279:ℝ)/21094400) = (6794240:ℝ)/4239373 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84793279:ℝ)/21094400)-4 = (415679:ℝ)/21094400 by norm_num]
    exact paid_middle_821
  · change middlePayment 822 ≤ middleValue ((point 4 cut 1024 822+point 4 cut 1024 823)/2)
    have hp : middlePayment 822 = (658015996984:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 822+point 4 cut 1024 823)/2 = (16958757:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16958757:ℝ)/4218880) = (33971200:ℝ)/21196359 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16958757:ℝ)/4218880)-4 = (83237:ℝ)/4218880 by norm_num]
    exact paid_middle_822
  · change middlePayment 823 ≤ middleValue ((point 4 cut 1024 823+point 4 cut 1024 824)/2)
    have hp : middlePayment 823 = (658056138863:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 823+point 4 cut 1024 824)/2 = (84794291:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84794291:ℝ)/21094400) = (33971200:ℝ)/21195853 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84794291:ℝ)/21094400)-4 = (416691:ℝ)/21094400 by norm_num]
    exact paid_middle_823
  · change middlePayment 824 ≤ middleValue ((point 4 cut 1024 824+point 4 cut 1024 825)/2)
    have hp : middlePayment 824 = (658096282310:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 824+point 4 cut 1024 825)/2 = (84794797:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84794797:ℝ)/21094400) = (33971200:ℝ)/21195347 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84794797:ℝ)/21094400)-4 = (417197:ℝ)/21094400 by norm_num]
    exact paid_middle_824
  · change middlePayment 825 ≤ middleValue ((point 4 cut 1024 825+point 4 cut 1024 826)/2)
    have hp : middlePayment 825 = (658136427322:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 825+point 4 cut 1024 826)/2 = (84795303:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84795303:ℝ)/21094400) = (33971200:ℝ)/21194841 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84795303:ℝ)/21094400)-4 = (417703:ℝ)/21094400 by norm_num]
    exact paid_middle_825
  · change middlePayment 826 ≤ middleValue ((point 4 cut 1024 826+point 4 cut 1024 827)/2)
    have hp : middlePayment 826 = (658176573902:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 826+point 4 cut 1024 827)/2 = (84795809:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84795809:ℝ)/21094400) = (6794240:ℝ)/4238867 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84795809:ℝ)/21094400)-4 = (418209:ℝ)/21094400 by norm_num]
    exact paid_middle_826
  · change middlePayment 827 ≤ middleValue ((point 4 cut 1024 827+point 4 cut 1024 828)/2)
    have hp : middlePayment 827 = (658216722049:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 827+point 4 cut 1024 828)/2 = (16959263:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16959263:ℝ)/4218880) = (33971200:ℝ)/21193829 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16959263:ℝ)/4218880)-4 = (83743:ℝ)/4218880 by norm_num]
    exact paid_middle_827
  · change middlePayment 828 ≤ middleValue ((point 4 cut 1024 828+point 4 cut 1024 829)/2)
    have hp : middlePayment 828 = (658256871763:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 828+point 4 cut 1024 829)/2 = (84796821:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84796821:ℝ)/21094400) = (33971200:ℝ)/21193323 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84796821:ℝ)/21094400)-4 = (419221:ℝ)/21094400 by norm_num]
    exact paid_middle_828
  · change middlePayment 829 ≤ middleValue ((point 4 cut 1024 829+point 4 cut 1024 830)/2)
    have hp : middlePayment 829 = (658297023044:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 829+point 4 cut 1024 830)/2 = (84797327:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84797327:ℝ)/21094400) = (33971200:ℝ)/21192817 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84797327:ℝ)/21094400)-4 = (419727:ℝ)/21094400 by norm_num]
    exact paid_middle_829
  · change middlePayment 830 ≤ middleValue ((point 4 cut 1024 830+point 4 cut 1024 831)/2)
    have hp : middlePayment 830 = (658337175892:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 830+point 4 cut 1024 831)/2 = (84797833:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84797833:ℝ)/21094400) = (33971200:ℝ)/21192311 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84797833:ℝ)/21094400)-4 = (420233:ℝ)/21094400 by norm_num]
    exact paid_middle_830
  · change middlePayment 831 ≤ middleValue ((point 4 cut 1024 831+point 4 cut 1024 832)/2)
    have hp : middlePayment 831 = (658377330307:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 831+point 4 cut 1024 832)/2 = (84798339:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84798339:ℝ)/21094400) = (6794240:ℝ)/4238361 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84798339:ℝ)/21094400)-4 = (420739:ℝ)/21094400 by norm_num]
    exact paid_middle_831
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_051
