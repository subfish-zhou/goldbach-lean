import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints051
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_051 (j : Fin 16) : initialPayment (16*51+j.val) ≤
    initialValue ((point lo 4 1024 (16*51+j.val)+point lo 4 1024 (16*51+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 816 ≤ initialValue ((point lo 4 1024 816+point lo 4 1024 817)/2)
    have hp : initialPayment 816 = (450140355854:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 816+point lo 4 1024 817)/2 = (32749313:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32749313:ℝ)/8437760) = (67942400:ℝ)/48233723 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_816
  · change initialPayment 817 ≤ initialValue ((point lo 4 1024 817+point lo 4 1024 818)/2)
    have hp : initialPayment 817 = (450909852316:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 817+point lo 4 1024 818)/2 = (163770703:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163770703:ℝ)/42188800) = (13588480:ℝ)/9641917 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_817
  · change initialPayment 818 ≤ initialValue ((point lo 4 1024 818+point lo 4 1024 819)/2)
    have hp : initialPayment 818 = (451680028953:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 818+point lo 4 1024 819)/2 = (163794841:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163794841:ℝ)/42188800) = (67942400:ℝ)/48185447 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_818
  · change initialPayment 819 ≤ initialValue ((point lo 4 1024 819+point lo 4 1024 820)/2)
    have hp : initialPayment 819 = (452450886479:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 819+point lo 4 1024 820)/2 = (163818979:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163818979:ℝ)/42188800) = (67942400:ℝ)/48161309 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_819
  · change initialPayment 820 ≤ initialValue ((point lo 4 1024 820+point lo 4 1024 821)/2)
    have hp : initialPayment 820 = (453222425607:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 820+point lo 4 1024 821)/2 = (163843117:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163843117:ℝ)/42188800) = (67942400:ℝ)/48137171 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_820
  · change initialPayment 821 ≤ initialValue ((point lo 4 1024 821+point lo 4 1024 822)/2)
    have hp : initialPayment 821 = (453994647055:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 821+point lo 4 1024 822)/2 = (32773451:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32773451:ℝ)/8437760) = (67942400:ℝ)/48113033 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_821
  · change initialPayment 822 ≤ initialValue ((point lo 4 1024 822+point lo 4 1024 823)/2)
    have hp : initialPayment 822 = (454767551539:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 822+point lo 4 1024 823)/2 = (163891393:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163891393:ℝ)/42188800) = (13588480:ℝ)/9617779 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_822
  · change initialPayment 823 ≤ initialValue ((point lo 4 1024 823+point lo 4 1024 824)/2)
    have hp : initialPayment 823 = (455541139778:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 823+point lo 4 1024 824)/2 = (163915531:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163915531:ℝ)/42188800) = (67942400:ℝ)/48064757 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_823
  · change initialPayment 824 ≤ initialValue ((point lo 4 1024 824+point lo 4 1024 825)/2)
    have hp : initialPayment 824 = (456315412491:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 824+point lo 4 1024 825)/2 = (163939669:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163939669:ℝ)/42188800) = (67942400:ℝ)/48040619 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_824
  · change initialPayment 825 ≤ initialValue ((point lo 4 1024 825+point lo 4 1024 826)/2)
    have hp : initialPayment 825 = (457090370399:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 825+point lo 4 1024 826)/2 = (163963807:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163963807:ℝ)/42188800) = (67942400:ℝ)/48016481 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_825
  · change initialPayment 826 ≤ initialValue ((point lo 4 1024 826+point lo 4 1024 827)/2)
    have hp : initialPayment 826 = (457866014223:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 826+point lo 4 1024 827)/2 = (32797589:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32797589:ℝ)/8437760) = (67942400:ℝ)/47992343 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_826
  · change initialPayment 827 ≤ initialValue ((point lo 4 1024 827+point lo 4 1024 828)/2)
    have hp : initialPayment 827 = (458642344687:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 827+point lo 4 1024 828)/2 = (164012083:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164012083:ℝ)/42188800) = (13588480:ℝ)/9593641 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_827
  · change initialPayment 828 ≤ initialValue ((point lo 4 1024 828+point lo 4 1024 829)/2)
    have hp : initialPayment 828 = (459419362514:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 828+point lo 4 1024 829)/2 = (164036221:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164036221:ℝ)/42188800) = (67942400:ℝ)/47944067 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_828
  · change initialPayment 829 ≤ initialValue ((point lo 4 1024 829+point lo 4 1024 830)/2)
    have hp : initialPayment 829 = (460197068430:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 829+point lo 4 1024 830)/2 = (164060359:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164060359:ℝ)/42188800) = (67942400:ℝ)/47919929 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_829
  · change initialPayment 830 ≤ initialValue ((point lo 4 1024 830+point lo 4 1024 831)/2)
    have hp : initialPayment 830 = (460975463161:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 830+point lo 4 1024 831)/2 = (164084497:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164084497:ℝ)/42188800) = (67942400:ℝ)/47895791 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_830
  · change initialPayment 831 ≤ initialValue ((point lo 4 1024 831+point lo 4 1024 832)/2)
    have hp : initialPayment 831 = (461754547434:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 831+point lo 4 1024 832)/2 = (32821727:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32821727:ℝ)/8437760) = (67942400:ℝ)/47871653 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_831
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_051
