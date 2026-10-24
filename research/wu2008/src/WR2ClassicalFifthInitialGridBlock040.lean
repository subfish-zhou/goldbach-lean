import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints040
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_040 (j : Fin 16) : initialPayment (16*40+j.val) ≤
    initialValue ((point lo 4 1024 (16*40+j.val)+point lo 4 1024 (16*40+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 640 ≤ initialValue ((point lo 4 1024 640+point lo 4 1024 641)/2)
    have hp : initialPayment 640 = (324687415358:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 640+point lo 4 1024 641)/2 = (159498277:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159498277:ℝ)/42188800) = (67942400:ℝ)/52482011 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_640
  · change initialPayment 641 ≤ initialValue ((point lo 4 1024 641+point lo 4 1024 642)/2)
    have hp : initialPayment 641 = (325347357384:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 641+point lo 4 1024 642)/2 = (31904483:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31904483:ℝ)/8437760) = (67942400:ℝ)/52457873 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_641
  · change initialPayment 642 ≤ initialValue ((point lo 4 1024 642+point lo 4 1024 643)/2)
    have hp : initialPayment 642 = (326007869756:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 642+point lo 4 1024 643)/2 = (159546553:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159546553:ℝ)/42188800) = (13588480:ℝ)/10486747 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_642
  · change initialPayment 643 ≤ initialValue ((point lo 4 1024 643+point lo 4 1024 644)/2)
    have hp : initialPayment 643 = (326668953018:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 643+point lo 4 1024 644)/2 = (159570691:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159570691:ℝ)/42188800) = (67942400:ℝ)/52409597 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_643
  · change initialPayment 644 ≤ initialValue ((point lo 4 1024 644+point lo 4 1024 645)/2)
    have hp : initialPayment 644 = (327330607716:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 644+point lo 4 1024 645)/2 = (159594829:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159594829:ℝ)/42188800) = (67942400:ℝ)/52385459 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_644
  · change initialPayment 645 ≤ initialValue ((point lo 4 1024 645+point lo 4 1024 646)/2)
    have hp : initialPayment 645 = (327992834395:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 645+point lo 4 1024 646)/2 = (159618967:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159618967:ℝ)/42188800) = (67942400:ℝ)/52361321 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_645
  · change initialPayment 646 ≤ initialValue ((point lo 4 1024 646+point lo 4 1024 647)/2)
    have hp : initialPayment 646 = (328655633601:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 646+point lo 4 1024 647)/2 = (31928621:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31928621:ℝ)/8437760) = (67942400:ℝ)/52337183 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_646
  · change initialPayment 647 ≤ initialValue ((point lo 4 1024 647+point lo 4 1024 648)/2)
    have hp : initialPayment 647 = (329319005883:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 647+point lo 4 1024 648)/2 = (159667243:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159667243:ℝ)/42188800) = (13588480:ℝ)/10462609 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_647
  · change initialPayment 648 ≤ initialValue ((point lo 4 1024 648+point lo 4 1024 649)/2)
    have hp : initialPayment 648 = (329982951788:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 648+point lo 4 1024 649)/2 = (159691381:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159691381:ℝ)/42188800) = (67942400:ℝ)/52288907 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_648
  · change initialPayment 649 ≤ initialValue ((point lo 4 1024 649+point lo 4 1024 650)/2)
    have hp : initialPayment 649 = (330647471866:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 649+point lo 4 1024 650)/2 = (159715519:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159715519:ℝ)/42188800) = (67942400:ℝ)/52264769 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_649
  · change initialPayment 650 ≤ initialValue ((point lo 4 1024 650+point lo 4 1024 651)/2)
    have hp : initialPayment 650 = (331312566666:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 650+point lo 4 1024 651)/2 = (159739657:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159739657:ℝ)/42188800) = (67942400:ℝ)/52240631 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_650
  · change initialPayment 651 ≤ initialValue ((point lo 4 1024 651+point lo 4 1024 652)/2)
    have hp : initialPayment 651 = (331978236740:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 651+point lo 4 1024 652)/2 = (31952759:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31952759:ℝ)/8437760) = (67942400:ℝ)/52216493 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_651
  · change initialPayment 652 ≤ initialValue ((point lo 4 1024 652+point lo 4 1024 653)/2)
    have hp : initialPayment 652 = (332644482639:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 652+point lo 4 1024 653)/2 = (159787933:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159787933:ℝ)/42188800) = (13588480:ℝ)/10438471 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_652
  · change initialPayment 653 ≤ initialValue ((point lo 4 1024 653+point lo 4 1024 654)/2)
    have hp : initialPayment 653 = (333311304916:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 653+point lo 4 1024 654)/2 = (159812071:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159812071:ℝ)/42188800) = (67942400:ℝ)/52168217 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_653
  · change initialPayment 654 ≤ initialValue ((point lo 4 1024 654+point lo 4 1024 655)/2)
    have hp : initialPayment 654 = (333978704124:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 654+point lo 4 1024 655)/2 = (159836209:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159836209:ℝ)/42188800) = (67942400:ℝ)/52144079 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_654
  · change initialPayment 655 ≤ initialValue ((point lo 4 1024 655+point lo 4 1024 656)/2)
    have hp : initialPayment 655 = (334646680816:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 655+point lo 4 1024 656)/2 = (159860347:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159860347:ℝ)/42188800) = (67942400:ℝ)/52119941 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_655
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_040
