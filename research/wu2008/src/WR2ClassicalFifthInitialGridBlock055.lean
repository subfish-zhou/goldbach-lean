import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints055
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_055 (j : Fin 16) : initialPayment (16*55+j.val) ≤
    initialValue ((point lo 4 1024 (16*55+j.val)+point lo 4 1024 (16*55+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 880 ≤ initialValue ((point lo 4 1024 880+point lo 4 1024 881)/2)
    have hp : initialPayment 880 = (500789834938:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 880+point lo 4 1024 881)/2 = (165291397:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165291397:ℝ)/42188800) = (67942400:ℝ)/46688891 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_880
  · change initialPayment 881 ≤ initialValue ((point lo 4 1024 881+point lo 4 1024 882)/2)
    have hp : initialPayment 881 = (501604350026:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 881+point lo 4 1024 882)/2 = (33063107:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33063107:ℝ)/8437760) = (67942400:ℝ)/46664753 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_881
  · change initialPayment 882 ≤ initialValue ((point lo 4 1024 882+point lo 4 1024 883)/2)
    have hp : initialPayment 882 = (502419593339:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 882+point lo 4 1024 883)/2 = (165339673:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165339673:ℝ)/42188800) = (13588480:ℝ)/9328123 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_882
  · change initialPayment 883 ≤ initialValue ((point lo 4 1024 883+point lo 4 1024 884)/2)
    have hp : initialPayment 883 = (503235565670:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 883+point lo 4 1024 884)/2 = (165363811:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165363811:ℝ)/42188800) = (67942400:ℝ)/46616477 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_883
  · change initialPayment 884 ≤ initialValue ((point lo 4 1024 884+point lo 4 1024 885)/2)
    have hp : initialPayment 884 = (504052267810:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 884+point lo 4 1024 885)/2 = (165387949:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165387949:ℝ)/42188800) = (67942400:ℝ)/46592339 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_884
  · change initialPayment 885 ≤ initialValue ((point lo 4 1024 885+point lo 4 1024 886)/2)
    have hp : initialPayment 885 = (504869700551:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 885+point lo 4 1024 886)/2 = (165412087:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165412087:ℝ)/42188800) = (67942400:ℝ)/46568201 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_885
  · change initialPayment 886 ≤ initialValue ((point lo 4 1024 886+point lo 4 1024 887)/2)
    have hp : initialPayment 886 = (505687864689:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 886+point lo 4 1024 887)/2 = (6617449:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6617449:ℝ)/1687552) = (67942400:ℝ)/46544063 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_886
  · change initialPayment 887 ≤ initialValue ((point lo 4 1024 887+point lo 4 1024 888)/2)
    have hp : initialPayment 887 = (506506761019:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 887+point lo 4 1024 888)/2 = (165460363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165460363:ℝ)/42188800) = (2717696:ℝ)/1860797 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_887
  · change initialPayment 888 ≤ initialValue ((point lo 4 1024 888+point lo 4 1024 889)/2)
    have hp : initialPayment 888 = (507326390339:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 888+point lo 4 1024 889)/2 = (165484501:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165484501:ℝ)/42188800) = (67942400:ℝ)/46495787 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_888
  · change initialPayment 889 ≤ initialValue ((point lo 4 1024 889+point lo 4 1024 890)/2)
    have hp : initialPayment 889 = (508146753446:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 889+point lo 4 1024 890)/2 = (165508639:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165508639:ℝ)/42188800) = (67942400:ℝ)/46471649 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_889
  · change initialPayment 890 ≤ initialValue ((point lo 4 1024 890+point lo 4 1024 891)/2)
    have hp : initialPayment 890 = (508967851140:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 890+point lo 4 1024 891)/2 = (165532777:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165532777:ℝ)/42188800) = (67942400:ℝ)/46447511 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_890
  · change initialPayment 891 ≤ initialValue ((point lo 4 1024 891+point lo 4 1024 892)/2)
    have hp : initialPayment 891 = (509789684222:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 891+point lo 4 1024 892)/2 = (33111383:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33111383:ℝ)/8437760) = (67942400:ℝ)/46423373 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_891
  · change initialPayment 892 ≤ initialValue ((point lo 4 1024 892+point lo 4 1024 893)/2)
    have hp : initialPayment 892 = (510612253494:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 892+point lo 4 1024 893)/2 = (165581053:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165581053:ℝ)/42188800) = (13588480:ℝ)/9279847 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_892
  · change initialPayment 893 ≤ initialValue ((point lo 4 1024 893+point lo 4 1024 894)/2)
    have hp : initialPayment 893 = (511435559760:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 893+point lo 4 1024 894)/2 = (165605191:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165605191:ℝ)/42188800) = (67942400:ℝ)/46375097 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_893
  · change initialPayment 894 ≤ initialValue ((point lo 4 1024 894+point lo 4 1024 895)/2)
    have hp : initialPayment 894 = (512259603824:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 894+point lo 4 1024 895)/2 = (165629329:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165629329:ℝ)/42188800) = (67942400:ℝ)/46350959 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_894
  · change initialPayment 895 ≤ initialValue ((point lo 4 1024 895+point lo 4 1024 896)/2)
    have hp : initialPayment 895 = (513084386493:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 895+point lo 4 1024 896)/2 = (165653467:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165653467:ℝ)/42188800) = (67942400:ℝ)/46326821 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_895
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_055
