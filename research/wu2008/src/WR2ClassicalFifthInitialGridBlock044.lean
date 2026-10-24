import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints044
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_044 (j : Fin 16) : initialPayment (16*44+j.val) ≤
    initialValue ((point lo 4 1024 (16*44+j.val)+point lo 4 1024 (16*44+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 704 ≤ initialValue ((point lo 4 1024 704+point lo 4 1024 705)/2)
    have hp : initialPayment 704 = (368096728821:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 704+point lo 4 1024 705)/2 = (161043109:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161043109:ℝ)/42188800) = (67942400:ℝ)/50937179 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_704
  · change initialPayment 705 ≤ initialValue ((point lo 4 1024 705+point lo 4 1024 706)/2)
    have hp : initialPayment 705 = (368794305232:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 705+point lo 4 1024 706)/2 = (161067247:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161067247:ℝ)/42188800) = (67942400:ℝ)/50913041 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_705
  · change initialPayment 706 ≤ initialValue ((point lo 4 1024 706+point lo 4 1024 707)/2)
    have hp : initialPayment 706 = (369492488535:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 706+point lo 4 1024 707)/2 = (32218277:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32218277:ℝ)/8437760) = (67942400:ℝ)/50888903 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_706
  · change initialPayment 707 ≤ initialValue ((point lo 4 1024 707+point lo 4 1024 708)/2)
    have hp : initialPayment 707 = (370191279330:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 707+point lo 4 1024 708)/2 = (161115523:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161115523:ℝ)/42188800) = (13588480:ℝ)/10172953 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_707
  · change initialPayment 708 ≤ initialValue ((point lo 4 1024 708+point lo 4 1024 709)/2)
    have hp : initialPayment 708 = (370890678216:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 708+point lo 4 1024 709)/2 = (161139661:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161139661:ℝ)/42188800) = (67942400:ℝ)/50840627 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_708
  · change initialPayment 709 ≤ initialValue ((point lo 4 1024 709+point lo 4 1024 710)/2)
    have hp : initialPayment 709 = (371590685795:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 709+point lo 4 1024 710)/2 = (161163799:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161163799:ℝ)/42188800) = (67942400:ℝ)/50816489 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_709
  · change initialPayment 710 ≤ initialValue ((point lo 4 1024 710+point lo 4 1024 711)/2)
    have hp : initialPayment 710 = (372291302670:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 710+point lo 4 1024 711)/2 = (161187937:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161187937:ℝ)/42188800) = (67942400:ℝ)/50792351 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_710
  · change initialPayment 711 ≤ initialValue ((point lo 4 1024 711+point lo 4 1024 712)/2)
    have hp : initialPayment 711 = (372992529445:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 711+point lo 4 1024 712)/2 = (6448483:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6448483:ℝ)/1687552) = (67942400:ℝ)/50768213 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_711
  · change initialPayment 712 ≤ initialValue ((point lo 4 1024 712+point lo 4 1024 713)/2)
    have hp : initialPayment 712 = (373694366723:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 712+point lo 4 1024 713)/2 = (161236213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161236213:ℝ)/42188800) = (2717696:ℝ)/2029763 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_712
  · change initialPayment 713 ≤ initialValue ((point lo 4 1024 713+point lo 4 1024 714)/2)
    have hp : initialPayment 713 = (374396815110:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 713+point lo 4 1024 714)/2 = (161260351:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161260351:ℝ)/42188800) = (67942400:ℝ)/50719937 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_713
  · change initialPayment 714 ≤ initialValue ((point lo 4 1024 714+point lo 4 1024 715)/2)
    have hp : initialPayment 714 = (375099875213:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 714+point lo 4 1024 715)/2 = (161284489:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161284489:ℝ)/42188800) = (67942400:ℝ)/50695799 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_714
  · change initialPayment 715 ≤ initialValue ((point lo 4 1024 715+point lo 4 1024 716)/2)
    have hp : initialPayment 715 = (375803547638:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 715+point lo 4 1024 716)/2 = (161308627:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161308627:ℝ)/42188800) = (67942400:ℝ)/50671661 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_715
  · change initialPayment 716 ≤ initialValue ((point lo 4 1024 716+point lo 4 1024 717)/2)
    have hp : initialPayment 716 = (376507832993:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 716+point lo 4 1024 717)/2 = (32266553:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32266553:ℝ)/8437760) = (67942400:ℝ)/50647523 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_716
  · change initialPayment 717 ≤ initialValue ((point lo 4 1024 717+point lo 4 1024 718)/2)
    have hp : initialPayment 717 = (377212731888:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 717+point lo 4 1024 718)/2 = (161356903:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161356903:ℝ)/42188800) = (13588480:ℝ)/10124677 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_717
  · change initialPayment 718 ≤ initialValue ((point lo 4 1024 718+point lo 4 1024 719)/2)
    have hp : initialPayment 718 = (377918244932:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 718+point lo 4 1024 719)/2 = (161381041:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161381041:ℝ)/42188800) = (67942400:ℝ)/50599247 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_718
  · change initialPayment 719 ≤ initialValue ((point lo 4 1024 719+point lo 4 1024 720)/2)
    have hp : initialPayment 719 = (378624372736:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 719+point lo 4 1024 720)/2 = (161405179:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161405179:ℝ)/42188800) = (67942400:ℝ)/50575109 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_719
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_044
