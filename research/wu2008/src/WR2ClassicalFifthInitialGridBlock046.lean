import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints046
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_046 (j : Fin 16) : initialPayment (16*46+j.val) ≤
    initialValue ((point lo 4 1024 (16*46+j.val)+point lo 4 1024 (16*46+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 736 ≤ initialValue ((point lo 4 1024 736+point lo 4 1024 737)/2)
    have hp : initialPayment 736 = (390723200262:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 736+point lo 4 1024 737)/2 = (6472621:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6472621:ℝ)/1687552) = (67942400:ℝ)/50164763 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_736
  · change initialPayment 737 ≤ initialValue ((point lo 4 1024 737+point lo 4 1024 738)/2)
    have hp : initialPayment 737 = (391440499293:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 737+point lo 4 1024 738)/2 = (161839663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161839663:ℝ)/42188800) = (2717696:ℝ)/2005625 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_737
  · change initialPayment 738 ≤ initialValue ((point lo 4 1024 738+point lo 4 1024 739)/2)
    have hp : initialPayment 738 = (392158424870:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 738+point lo 4 1024 739)/2 = (161863801:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161863801:ℝ)/42188800) = (67942400:ℝ)/50116487 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_738
  · change initialPayment 739 ≤ initialValue ((point lo 4 1024 739+point lo 4 1024 740)/2)
    have hp : initialPayment 739 = (392876977626:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 739+point lo 4 1024 740)/2 = (161887939:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161887939:ℝ)/42188800) = (67942400:ℝ)/50092349 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_739
  · change initialPayment 740 ≤ initialValue ((point lo 4 1024 740+point lo 4 1024 741)/2)
    have hp : initialPayment 740 = (393596158189:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 740+point lo 4 1024 741)/2 = (161912077:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161912077:ℝ)/42188800) = (67942400:ℝ)/50068211 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_740
  · change initialPayment 741 ≤ initialValue ((point lo 4 1024 741+point lo 4 1024 742)/2)
    have hp : initialPayment 741 = (394315967193:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 741+point lo 4 1024 742)/2 = (32387243:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32387243:ℝ)/8437760) = (67942400:ℝ)/50044073 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_741
  · change initialPayment 742 ≤ initialValue ((point lo 4 1024 742+point lo 4 1024 743)/2)
    have hp : initialPayment 742 = (395036405271:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 742+point lo 4 1024 743)/2 = (161960353:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161960353:ℝ)/42188800) = (13588480:ℝ)/10003987 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_742
  · change initialPayment 743 ≤ initialValue ((point lo 4 1024 743+point lo 4 1024 744)/2)
    have hp : initialPayment 743 = (395757473055:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 743+point lo 4 1024 744)/2 = (161984491:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161984491:ℝ)/42188800) = (67942400:ℝ)/49995797 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_743
  · change initialPayment 744 ≤ initialValue ((point lo 4 1024 744+point lo 4 1024 745)/2)
    have hp : initialPayment 744 = (396479171182:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 744+point lo 4 1024 745)/2 = (162008629:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162008629:ℝ)/42188800) = (67942400:ℝ)/49971659 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_744
  · change initialPayment 745 ≤ initialValue ((point lo 4 1024 745+point lo 4 1024 746)/2)
    have hp : initialPayment 745 = (397201500286:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 745+point lo 4 1024 746)/2 = (162032767:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162032767:ℝ)/42188800) = (67942400:ℝ)/49947521 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_745
  · change initialPayment 746 ≤ initialValue ((point lo 4 1024 746+point lo 4 1024 747)/2)
    have hp : initialPayment 746 = (397924461006:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 746+point lo 4 1024 747)/2 = (32411381:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32411381:ℝ)/8437760) = (67942400:ℝ)/49923383 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_746
  · change initialPayment 747 ≤ initialValue ((point lo 4 1024 747+point lo 4 1024 748)/2)
    have hp : initialPayment 747 = (398648053978:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 747+point lo 4 1024 748)/2 = (162081043:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162081043:ℝ)/42188800) = (13588480:ℝ)/9979849 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_747
  · change initialPayment 748 ≤ initialValue ((point lo 4 1024 748+point lo 4 1024 749)/2)
    have hp : initialPayment 748 = (399372279841:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 748+point lo 4 1024 749)/2 = (162105181:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162105181:ℝ)/42188800) = (67942400:ℝ)/49875107 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_748
  · change initialPayment 749 ≤ initialValue ((point lo 4 1024 749+point lo 4 1024 750)/2)
    have hp : initialPayment 749 = (400097139235:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 749+point lo 4 1024 750)/2 = (162129319:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162129319:ℝ)/42188800) = (67942400:ℝ)/49850969 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_749
  · change initialPayment 750 ≤ initialValue ((point lo 4 1024 750+point lo 4 1024 751)/2)
    have hp : initialPayment 750 = (400822632802:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 750+point lo 4 1024 751)/2 = (162153457:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162153457:ℝ)/42188800) = (67942400:ℝ)/49826831 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_750
  · change initialPayment 751 ≤ initialValue ((point lo 4 1024 751+point lo 4 1024 752)/2)
    have hp : initialPayment 751 = (401548761182:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 751+point lo 4 1024 752)/2 = (32435519:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32435519:ℝ)/8437760) = (67942400:ℝ)/49802693 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_751
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_046
