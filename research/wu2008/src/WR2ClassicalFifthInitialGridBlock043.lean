import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints043
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_043 (j : Fin 16) : initialPayment (16*43+j.val) ≤
    initialValue ((point lo 4 1024 (16*43+j.val)+point lo 4 1024 (16*43+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 688 ≤ initialValue ((point lo 4 1024 688+point lo 4 1024 689)/2)
    have hp : initialPayment 688 = (357017557593:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 688+point lo 4 1024 689)/2 = (160656901:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160656901:ℝ)/42188800) = (67942400:ℝ)/51323387 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_688
  · change initialPayment 689 ≤ initialValue ((point lo 4 1024 689+point lo 4 1024 690)/2)
    have hp : initialPayment 689 = (357705504566:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 689+point lo 4 1024 690)/2 = (160681039:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160681039:ℝ)/42188800) = (67942400:ℝ)/51299249 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_689
  · change initialPayment 690 ≤ initialValue ((point lo 4 1024 690+point lo 4 1024 691)/2)
    have hp : initialPayment 690 = (358394048959:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 690+point lo 4 1024 691)/2 = (160705177:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160705177:ℝ)/42188800) = (67942400:ℝ)/51275111 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_690
  · change initialPayment 691 ≤ initialValue ((point lo 4 1024 691+point lo 4 1024 692)/2)
    have hp : initialPayment 691 = (359083191355:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 691+point lo 4 1024 692)/2 = (32145863:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32145863:ℝ)/8437760) = (67942400:ℝ)/51250973 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_691
  · change initialPayment 692 ≤ initialValue ((point lo 4 1024 692+point lo 4 1024 693)/2)
    have hp : initialPayment 692 = (359772932342:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 692+point lo 4 1024 693)/2 = (160753453:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160753453:ℝ)/42188800) = (13588480:ℝ)/10245367 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_692
  · change initialPayment 693 ≤ initialValue ((point lo 4 1024 693+point lo 4 1024 694)/2)
    have hp : initialPayment 693 = (360463272506:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 693+point lo 4 1024 694)/2 = (160777591:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160777591:ℝ)/42188800) = (67942400:ℝ)/51202697 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_693
  · change initialPayment 694 ≤ initialValue ((point lo 4 1024 694+point lo 4 1024 695)/2)
    have hp : initialPayment 694 = (361154212435:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 694+point lo 4 1024 695)/2 = (160801729:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160801729:ℝ)/42188800) = (67942400:ℝ)/51178559 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_694
  · change initialPayment 695 ≤ initialValue ((point lo 4 1024 695+point lo 4 1024 696)/2)
    have hp : initialPayment 695 = (361845752719:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 695+point lo 4 1024 696)/2 = (160825867:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160825867:ℝ)/42188800) = (67942400:ℝ)/51154421 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_695
  · change initialPayment 696 ≤ initialValue ((point lo 4 1024 696+point lo 4 1024 697)/2)
    have hp : initialPayment 696 = (362537893947:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 696+point lo 4 1024 697)/2 = (32170001:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32170001:ℝ)/8437760) = (67942400:ℝ)/51130283 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_696
  · change initialPayment 697 ≤ initialValue ((point lo 4 1024 697+point lo 4 1024 698)/2)
    have hp : initialPayment 697 = (363230636709:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 697+point lo 4 1024 698)/2 = (160874143:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160874143:ℝ)/42188800) = (13588480:ℝ)/10221229 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_697
  · change initialPayment 698 ≤ initialValue ((point lo 4 1024 698+point lo 4 1024 699)/2)
    have hp : initialPayment 698 = (363923981598:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 698+point lo 4 1024 699)/2 = (160898281:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160898281:ℝ)/42188800) = (67942400:ℝ)/51082007 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_698
  · change initialPayment 699 ≤ initialValue ((point lo 4 1024 699+point lo 4 1024 700)/2)
    have hp : initialPayment 699 = (364617929205:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 699+point lo 4 1024 700)/2 = (160922419:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160922419:ℝ)/42188800) = (67942400:ℝ)/51057869 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_699
  · change initialPayment 700 ≤ initialValue ((point lo 4 1024 700+point lo 4 1024 701)/2)
    have hp : initialPayment 700 = (365312480124:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 700+point lo 4 1024 701)/2 = (160946557:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160946557:ℝ)/42188800) = (67942400:ℝ)/51033731 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_700
  · change initialPayment 701 ≤ initialValue ((point lo 4 1024 701+point lo 4 1024 702)/2)
    have hp : initialPayment 701 = (366007634950:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 701+point lo 4 1024 702)/2 = (32194139:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32194139:ℝ)/8437760) = (67942400:ℝ)/51009593 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_701
  · change initialPayment 702 ≤ initialValue ((point lo 4 1024 702+point lo 4 1024 703)/2)
    have hp : initialPayment 702 = (366703394277:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 702+point lo 4 1024 703)/2 = (160994833:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160994833:ℝ)/42188800) = (13588480:ℝ)/10197091 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_702
  · change initialPayment 703 ≤ initialValue ((point lo 4 1024 703+point lo 4 1024 704)/2)
    have hp : initialPayment 703 = (367399758701:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 703+point lo 4 1024 704)/2 = (161018971:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161018971:ℝ)/42188800) = (67942400:ℝ)/50961317 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_703
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_043
