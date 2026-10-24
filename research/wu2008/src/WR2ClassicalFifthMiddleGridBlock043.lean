import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints043
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_043 (j : Fin 16) : middlePayment (16*43+j.val) ≤
    middleValue ((point 4 cut 1024 (16*43+j.val)+point 4 cut 1024 (16*43+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 688 ≤ middleValue ((point 4 cut 1024 688+point 4 cut 1024 689)/2)
    have hp : middlePayment 688 = (652651123168:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 688+point 4 cut 1024 689)/2 = (84725981:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84725981:ℝ)/21094400) = (33971200:ℝ)/21264163 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84725981:ℝ)/21094400)-4 = (348381:ℝ)/21094400 by norm_num]
    exact paid_middle_688
  · change middlePayment 689 ≤ middleValue ((point 4 cut 1024 689+point 4 cut 1024 690)/2)
    have hp : middlePayment 689 = (652691055830:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 689+point 4 cut 1024 690)/2 = (84726487:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84726487:ℝ)/21094400) = (33971200:ℝ)/21263657 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84726487:ℝ)/21094400)-4 = (348887:ℝ)/21094400 by norm_num]
    exact paid_middle_689
  · change middlePayment 690 ≤ middleValue ((point 4 cut 1024 690+point 4 cut 1024 691)/2)
    have hp : middlePayment 690 = (652730990049:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 690+point 4 cut 1024 691)/2 = (84726993:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84726993:ℝ)/21094400) = (33971200:ℝ)/21263151 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84726993:ℝ)/21094400)-4 = (349393:ℝ)/21094400 by norm_num]
    exact paid_middle_690
  · change middlePayment 691 ≤ middleValue ((point 4 cut 1024 691+point 4 cut 1024 692)/2)
    have hp : middlePayment 691 = (652770925824:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 691+point 4 cut 1024 692)/2 = (84727499:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84727499:ℝ)/21094400) = (6794240:ℝ)/4252529 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84727499:ℝ)/21094400)-4 = (349899:ℝ)/21094400 by norm_num]
    exact paid_middle_691
  · change middlePayment 692 ≤ middleValue ((point 4 cut 1024 692+point 4 cut 1024 693)/2)
    have hp : middlePayment 692 = (652810863155:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 692+point 4 cut 1024 693)/2 = (16945601:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16945601:ℝ)/4218880) = (33971200:ℝ)/21262139 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16945601:ℝ)/4218880)-4 = (70081:ℝ)/4218880 by norm_num]
    exact paid_middle_692
  · change middlePayment 693 ≤ middleValue ((point 4 cut 1024 693+point 4 cut 1024 694)/2)
    have hp : middlePayment 693 = (652850802042:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 693+point 4 cut 1024 694)/2 = (84728511:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84728511:ℝ)/21094400) = (33971200:ℝ)/21261633 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84728511:ℝ)/21094400)-4 = (350911:ℝ)/21094400 by norm_num]
    exact paid_middle_693
  · change middlePayment 694 ≤ middleValue ((point 4 cut 1024 694+point 4 cut 1024 695)/2)
    have hp : middlePayment 694 = (652890742486:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 694+point 4 cut 1024 695)/2 = (84729017:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84729017:ℝ)/21094400) = (33971200:ℝ)/21261127 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84729017:ℝ)/21094400)-4 = (351417:ℝ)/21094400 by norm_num]
    exact paid_middle_694
  · change middlePayment 695 ≤ middleValue ((point 4 cut 1024 695+point 4 cut 1024 696)/2)
    have hp : middlePayment 695 = (652930684486:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 695+point 4 cut 1024 696)/2 = (84729523:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84729523:ℝ)/21094400) = (33971200:ℝ)/21260621 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84729523:ℝ)/21094400)-4 = (351923:ℝ)/21094400 by norm_num]
    exact paid_middle_695
  · change middlePayment 696 ≤ middleValue ((point 4 cut 1024 696+point 4 cut 1024 697)/2)
    have hp : middlePayment 696 = (652970628043:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 696+point 4 cut 1024 697)/2 = (84730029:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84730029:ℝ)/21094400) = (6794240:ℝ)/4252023 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84730029:ℝ)/21094400)-4 = (352429:ℝ)/21094400 by norm_num]
    exact paid_middle_696
  · change middlePayment 697 ≤ middleValue ((point 4 cut 1024 697+point 4 cut 1024 698)/2)
    have hp : middlePayment 697 = (653010573156:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 697+point 4 cut 1024 698)/2 = (16946107:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16946107:ℝ)/4218880) = (33971200:ℝ)/21259609 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16946107:ℝ)/4218880)-4 = (70587:ℝ)/4218880 by norm_num]
    exact paid_middle_697
  · change middlePayment 698 ≤ middleValue ((point 4 cut 1024 698+point 4 cut 1024 699)/2)
    have hp : middlePayment 698 = (653050519826:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 698+point 4 cut 1024 699)/2 = (84731041:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84731041:ℝ)/21094400) = (33971200:ℝ)/21259103 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84731041:ℝ)/21094400)-4 = (353441:ℝ)/21094400 by norm_num]
    exact paid_middle_698
  · change middlePayment 699 ≤ middleValue ((point 4 cut 1024 699+point 4 cut 1024 700)/2)
    have hp : middlePayment 699 = (653090468053:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 699+point 4 cut 1024 700)/2 = (84731547:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84731547:ℝ)/21094400) = (33971200:ℝ)/21258597 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84731547:ℝ)/21094400)-4 = (353947:ℝ)/21094400 by norm_num]
    exact paid_middle_699
  · change middlePayment 700 ≤ middleValue ((point 4 cut 1024 700+point 4 cut 1024 701)/2)
    have hp : middlePayment 700 = (653130417836:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 700+point 4 cut 1024 701)/2 = (84732053:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84732053:ℝ)/21094400) = (33971200:ℝ)/21258091 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84732053:ℝ)/21094400)-4 = (354453:ℝ)/21094400 by norm_num]
    exact paid_middle_700
  · change middlePayment 701 ≤ middleValue ((point 4 cut 1024 701+point 4 cut 1024 702)/2)
    have hp : middlePayment 701 = (653170369177:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 701+point 4 cut 1024 702)/2 = (84732559:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84732559:ℝ)/21094400) = (6794240:ℝ)/4251517 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84732559:ℝ)/21094400)-4 = (354959:ℝ)/21094400 by norm_num]
    exact paid_middle_701
  · change middlePayment 702 ≤ middleValue ((point 4 cut 1024 702+point 4 cut 1024 703)/2)
    have hp : middlePayment 702 = (653210322074:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 702+point 4 cut 1024 703)/2 = (16946613:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16946613:ℝ)/4218880) = (33971200:ℝ)/21257079 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16946613:ℝ)/4218880)-4 = (71093:ℝ)/4218880 by norm_num]
    exact paid_middle_702
  · change middlePayment 703 ≤ middleValue ((point 4 cut 1024 703+point 4 cut 1024 704)/2)
    have hp : middlePayment 703 = (653250276529:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 703+point 4 cut 1024 704)/2 = (84733571:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84733571:ℝ)/21094400) = (33971200:ℝ)/21256573 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84733571:ℝ)/21094400)-4 = (355971:ℝ)/21094400 by norm_num]
    exact paid_middle_703
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_043
