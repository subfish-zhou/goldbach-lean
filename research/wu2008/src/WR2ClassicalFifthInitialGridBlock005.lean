import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints005
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_005 (j : Fin 16) : initialPayment (16*5+j.val) ≤
    initialValue ((point lo 4 1024 (16*5+j.val)+point lo 4 1024 (16*5+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 80 ≤ initialValue ((point lo 4 1024 80+point lo 4 1024 81)/2)
    have hp : initialPayment 80 = (31553780340:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 80+point lo 4 1024 81)/2 = (145980997:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145980997:ℝ)/42188800) = (67942400:ℝ)/65999291 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_80
  · change initialPayment 81 ≤ initialValue ((point lo 4 1024 81+point lo 4 1024 82)/2)
    have hp : initialPayment 81 = (31960296861:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 81+point lo 4 1024 82)/2 = (29201027:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29201027:ℝ)/8437760) = (67942400:ℝ)/65975153 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_81
  · change initialPayment 82 ≤ initialValue ((point lo 4 1024 82+point lo 4 1024 83)/2)
    have hp : initialPayment 82 = (32367176625:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 82+point lo 4 1024 83)/2 = (146029273:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146029273:ℝ)/42188800) = (13588480:ℝ)/13190203 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_82
  · change initialPayment 83 ≤ initialValue ((point lo 4 1024 83+point lo 4 1024 84)/2)
    have hp : initialPayment 83 = (32774419869:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 83+point lo 4 1024 84)/2 = (146053411:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146053411:ℝ)/42188800) = (67942400:ℝ)/65926877 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_83
  · change initialPayment 84 ≤ initialValue ((point lo 4 1024 84+point lo 4 1024 85)/2)
    have hp : initialPayment 84 = (33182026833:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 84+point lo 4 1024 85)/2 = (146077549:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146077549:ℝ)/42188800) = (67942400:ℝ)/65902739 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_84
  · change initialPayment 85 ≤ initialValue ((point lo 4 1024 85+point lo 4 1024 86)/2)
    have hp : initialPayment 85 = (33589997753:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 85+point lo 4 1024 86)/2 = (146101687:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146101687:ℝ)/42188800) = (67942400:ℝ)/65878601 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_85
  · change initialPayment 86 ≤ initialValue ((point lo 4 1024 86+point lo 4 1024 87)/2)
    have hp : initialPayment 86 = (33998332869:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 86+point lo 4 1024 87)/2 = (5845033:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5845033:ℝ)/1687552) = (67942400:ℝ)/65854463 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_86
  · change initialPayment 87 ≤ initialValue ((point lo 4 1024 87+point lo 4 1024 88)/2)
    have hp : initialPayment 87 = (34407032420:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 87+point lo 4 1024 88)/2 = (146149963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146149963:ℝ)/42188800) = (2717696:ℝ)/2633213 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_87
  · change initialPayment 88 ≤ initialValue ((point lo 4 1024 88+point lo 4 1024 89)/2)
    have hp : initialPayment 88 = (34816096645:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 88+point lo 4 1024 89)/2 = (146174101:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146174101:ℝ)/42188800) = (67942400:ℝ)/65806187 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_88
  · change initialPayment 89 ≤ initialValue ((point lo 4 1024 89+point lo 4 1024 90)/2)
    have hp : initialPayment 89 = (35225525785:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 89+point lo 4 1024 90)/2 = (146198239:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146198239:ℝ)/42188800) = (67942400:ℝ)/65782049 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_89
  · change initialPayment 90 ≤ initialValue ((point lo 4 1024 90+point lo 4 1024 91)/2)
    have hp : initialPayment 90 = (35635320080:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 90+point lo 4 1024 91)/2 = (146222377:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146222377:ℝ)/42188800) = (67942400:ℝ)/65757911 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_90
  · change initialPayment 91 ≤ initialValue ((point lo 4 1024 91+point lo 4 1024 92)/2)
    have hp : initialPayment 91 = (36045479770:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 91+point lo 4 1024 92)/2 = (29249303:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29249303:ℝ)/8437760) = (67942400:ℝ)/65733773 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_91
  · change initialPayment 92 ≤ initialValue ((point lo 4 1024 92+point lo 4 1024 93)/2)
    have hp : initialPayment 92 = (36456005096:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 92+point lo 4 1024 93)/2 = (146270653:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146270653:ℝ)/42188800) = (13588480:ℝ)/13141927 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_92
  · change initialPayment 93 ≤ initialValue ((point lo 4 1024 93+point lo 4 1024 94)/2)
    have hp : initialPayment 93 = (36866896299:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 93+point lo 4 1024 94)/2 = (146294791:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146294791:ℝ)/42188800) = (67942400:ℝ)/65685497 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_93
  · change initialPayment 94 ≤ initialValue ((point lo 4 1024 94+point lo 4 1024 95)/2)
    have hp : initialPayment 94 = (37278153622:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 94+point lo 4 1024 95)/2 = (146318929:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146318929:ℝ)/42188800) = (67942400:ℝ)/65661359 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_94
  · change initialPayment 95 ≤ initialValue ((point lo 4 1024 95+point lo 4 1024 96)/2)
    have hp : initialPayment 95 = (37689777307:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 95+point lo 4 1024 96)/2 = (146343067:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146343067:ℝ)/42188800) = (67942400:ℝ)/65637221 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_95
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_005
