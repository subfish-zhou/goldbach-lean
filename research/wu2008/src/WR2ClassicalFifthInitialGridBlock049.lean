import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints049
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_049 (j : Fin 16) : initialPayment (16*49+j.val) ≤
    initialValue ((point lo 4 1024 (16*49+j.val)+point lo 4 1024 (16*49+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 784 ≤ initialValue ((point lo 4 1024 784+point lo 4 1024 785)/2)
    have hp : initialPayment 784 = (425871388056:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 784+point lo 4 1024 785)/2 = (162974149:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162974149:ℝ)/42188800) = (67942400:ℝ)/49006139 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_784
  · change initialPayment 785 ≤ initialValue ((point lo 4 1024 785+point lo 4 1024 786)/2)
    have hp : initialPayment 785 = (426619489180:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 785+point lo 4 1024 786)/2 = (162998287:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162998287:ℝ)/42188800) = (67942400:ℝ)/48982001 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_785
  · change initialPayment 786 ≤ initialValue ((point lo 4 1024 786+point lo 4 1024 787)/2)
    have hp : initialPayment 786 = (427368248220:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 786+point lo 4 1024 787)/2 = (6520897:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6520897:ℝ)/1687552) = (67942400:ℝ)/48957863 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_786
  · change initialPayment 787 ≤ initialValue ((point lo 4 1024 787+point lo 4 1024 788)/2)
    have hp : initialPayment 787 = (428117665855:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 787+point lo 4 1024 788)/2 = (163046563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163046563:ℝ)/42188800) = (2717696:ℝ)/1957349 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_787
  · change initialPayment 788 ≤ initialValue ((point lo 4 1024 788+point lo 4 1024 789)/2)
    have hp : initialPayment 788 = (428867742765:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 788+point lo 4 1024 789)/2 = (163070701:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163070701:ℝ)/42188800) = (67942400:ℝ)/48909587 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_788
  · change initialPayment 789 ≤ initialValue ((point lo 4 1024 789+point lo 4 1024 790)/2)
    have hp : initialPayment 789 = (429618479631:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 789+point lo 4 1024 790)/2 = (163094839:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163094839:ℝ)/42188800) = (67942400:ℝ)/48885449 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_789
  · change initialPayment 790 ≤ initialValue ((point lo 4 1024 790+point lo 4 1024 791)/2)
    have hp : initialPayment 790 = (430369877134:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 790+point lo 4 1024 791)/2 = (163118977:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163118977:ℝ)/42188800) = (67942400:ℝ)/48861311 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_790
  · change initialPayment 791 ≤ initialValue ((point lo 4 1024 791+point lo 4 1024 792)/2)
    have hp : initialPayment 791 = (431121935959:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 791+point lo 4 1024 792)/2 = (32628623:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32628623:ℝ)/8437760) = (67942400:ℝ)/48837173 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_791
  · change initialPayment 792 ≤ initialValue ((point lo 4 1024 792+point lo 4 1024 793)/2)
    have hp : initialPayment 792 = (431874656788:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 792+point lo 4 1024 793)/2 = (163167253:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163167253:ℝ)/42188800) = (13588480:ℝ)/9762607 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_792
  · change initialPayment 793 ≤ initialValue ((point lo 4 1024 793+point lo 4 1024 794)/2)
    have hp : initialPayment 793 = (432628040308:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 793+point lo 4 1024 794)/2 = (163191391:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163191391:ℝ)/42188800) = (67942400:ℝ)/48788897 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_793
  · change initialPayment 794 ≤ initialValue ((point lo 4 1024 794+point lo 4 1024 795)/2)
    have hp : initialPayment 794 = (433382087203:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 794+point lo 4 1024 795)/2 = (163215529:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163215529:ℝ)/42188800) = (67942400:ℝ)/48764759 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_794
  · change initialPayment 795 ≤ initialValue ((point lo 4 1024 795+point lo 4 1024 796)/2)
    have hp : initialPayment 795 = (434136798163:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 795+point lo 4 1024 796)/2 = (163239667:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163239667:ℝ)/42188800) = (67942400:ℝ)/48740621 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_795
  · change initialPayment 796 ≤ initialValue ((point lo 4 1024 796+point lo 4 1024 797)/2)
    have hp : initialPayment 796 = (434892173875:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 796+point lo 4 1024 797)/2 = (32652761:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32652761:ℝ)/8437760) = (67942400:ℝ)/48716483 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_796
  · change initialPayment 797 ≤ initialValue ((point lo 4 1024 797+point lo 4 1024 798)/2)
    have hp : initialPayment 797 = (435648215028:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 797+point lo 4 1024 798)/2 = (163287943:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163287943:ℝ)/42188800) = (13588480:ℝ)/9738469 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_797
  · change initialPayment 798 ≤ initialValue ((point lo 4 1024 798+point lo 4 1024 799)/2)
    have hp : initialPayment 798 = (436404922313:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 798+point lo 4 1024 799)/2 = (163312081:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163312081:ℝ)/42188800) = (67942400:ℝ)/48668207 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_798
  · change initialPayment 799 ≤ initialValue ((point lo 4 1024 799+point lo 4 1024 800)/2)
    have hp : initialPayment 799 = (437162296423:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 799+point lo 4 1024 800)/2 = (163336219:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163336219:ℝ)/42188800) = (67942400:ℝ)/48644069 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_799
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_049
