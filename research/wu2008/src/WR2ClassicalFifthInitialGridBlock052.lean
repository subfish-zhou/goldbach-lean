import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints052
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_052 (j : Fin 16) : initialPayment (16*52+j.val) ≤
    initialValue ((point lo 4 1024 (16*52+j.val)+point lo 4 1024 (16*52+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 832 ≤ initialValue ((point lo 4 1024 832+point lo 4 1024 833)/2)
    have hp : initialPayment 832 = (462534321979:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 832+point lo 4 1024 833)/2 = (164132773:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164132773:ℝ)/42188800) = (13588480:ℝ)/9569503 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_832
  · change initialPayment 833 ≤ initialValue ((point lo 4 1024 833+point lo 4 1024 834)/2)
    have hp : initialPayment 833 = (463314787525:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 833+point lo 4 1024 834)/2 = (164156911:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164156911:ℝ)/42188800) = (67942400:ℝ)/47823377 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_833
  · change initialPayment 834 ≤ initialValue ((point lo 4 1024 834+point lo 4 1024 835)/2)
    have hp : initialPayment 834 = (464095944802:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 834+point lo 4 1024 835)/2 = (164181049:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164181049:ℝ)/42188800) = (67942400:ℝ)/47799239 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_834
  · change initialPayment 835 ≤ initialValue ((point lo 4 1024 835+point lo 4 1024 836)/2)
    have hp : initialPayment 835 = (464877794543:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 835+point lo 4 1024 836)/2 = (164205187:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164205187:ℝ)/42188800) = (67942400:ℝ)/47775101 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_835
  · change initialPayment 836 ≤ initialValue ((point lo 4 1024 836+point lo 4 1024 837)/2)
    have hp : initialPayment 836 = (465660337482:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 836+point lo 4 1024 837)/2 = (6569173:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6569173:ℝ)/1687552) = (67942400:ℝ)/47750963 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_836
  · change initialPayment 837 ≤ initialValue ((point lo 4 1024 837+point lo 4 1024 838)/2)
    have hp : initialPayment 837 = (466443574353:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 837+point lo 4 1024 838)/2 = (164253463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164253463:ℝ)/42188800) = (2717696:ℝ)/1909073 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_837
  · change initialPayment 838 ≤ initialValue ((point lo 4 1024 838+point lo 4 1024 839)/2)
    have hp : initialPayment 838 = (467227505891:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 838+point lo 4 1024 839)/2 = (164277601:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164277601:ℝ)/42188800) = (67942400:ℝ)/47702687 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_838
  · change initialPayment 839 ≤ initialValue ((point lo 4 1024 839+point lo 4 1024 840)/2)
    have hp : initialPayment 839 = (468012132833:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 839+point lo 4 1024 840)/2 = (164301739:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164301739:ℝ)/42188800) = (67942400:ℝ)/47678549 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_839
  · change initialPayment 840 ≤ initialValue ((point lo 4 1024 840+point lo 4 1024 841)/2)
    have hp : initialPayment 840 = (468797455917:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 840+point lo 4 1024 841)/2 = (164325877:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164325877:ℝ)/42188800) = (67942400:ℝ)/47654411 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_840
  · change initialPayment 841 ≤ initialValue ((point lo 4 1024 841+point lo 4 1024 842)/2)
    have hp : initialPayment 841 = (469583475883:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 841+point lo 4 1024 842)/2 = (32870003:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32870003:ℝ)/8437760) = (67942400:ℝ)/47630273 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_841
  · change initialPayment 842 ≤ initialValue ((point lo 4 1024 842+point lo 4 1024 843)/2)
    have hp : initialPayment 842 = (470370193470:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 842+point lo 4 1024 843)/2 = (164374153:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164374153:ℝ)/42188800) = (13588480:ℝ)/9521227 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_842
  · change initialPayment 843 ≤ initialValue ((point lo 4 1024 843+point lo 4 1024 844)/2)
    have hp : initialPayment 843 = (471157609421:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 843+point lo 4 1024 844)/2 = (164398291:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164398291:ℝ)/42188800) = (67942400:ℝ)/47581997 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_843
  · change initialPayment 844 ≤ initialValue ((point lo 4 1024 844+point lo 4 1024 845)/2)
    have hp : initialPayment 844 = (471945724477:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 844+point lo 4 1024 845)/2 = (164422429:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164422429:ℝ)/42188800) = (67942400:ℝ)/47557859 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_844
  · change initialPayment 845 ≤ initialValue ((point lo 4 1024 845+point lo 4 1024 846)/2)
    have hp : initialPayment 845 = (472734539383:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 845+point lo 4 1024 846)/2 = (164446567:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164446567:ℝ)/42188800) = (67942400:ℝ)/47533721 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_845
  · change initialPayment 846 ≤ initialValue ((point lo 4 1024 846+point lo 4 1024 847)/2)
    have hp : initialPayment 846 = (473524054883:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 846+point lo 4 1024 847)/2 = (32894141:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32894141:ℝ)/8437760) = (67942400:ℝ)/47509583 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_846
  · change initialPayment 847 ≤ initialValue ((point lo 4 1024 847+point lo 4 1024 848)/2)
    have hp : initialPayment 847 = (474314271725:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 847+point lo 4 1024 848)/2 = (164494843:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164494843:ℝ)/42188800) = (13588480:ℝ)/9497089 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_847
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_052
