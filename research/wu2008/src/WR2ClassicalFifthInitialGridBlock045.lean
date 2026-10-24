import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints045
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_045 (j : Fin 16) : initialPayment (16*45+j.val) ≤
    initialValue ((point lo 4 1024 (16*45+j.val)+point lo 4 1024 (16*45+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 720 ≤ initialValue ((point lo 4 1024 720+point lo 4 1024 721)/2)
    have hp : initialPayment 720 = (379331115913:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 720+point lo 4 1024 721)/2 = (161429317:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161429317:ℝ)/42188800) = (67942400:ℝ)/50550971 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_720
  · change initialPayment 721 ≤ initialValue ((point lo 4 1024 721+point lo 4 1024 722)/2)
    have hp : initialPayment 721 = (380038475074:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 721+point lo 4 1024 722)/2 = (32290691:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32290691:ℝ)/8437760) = (67942400:ℝ)/50526833 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_721
  · change initialPayment 722 ≤ initialValue ((point lo 4 1024 722+point lo 4 1024 723)/2)
    have hp : initialPayment 722 = (380746450834:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 722+point lo 4 1024 723)/2 = (161477593:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161477593:ℝ)/42188800) = (13588480:ℝ)/10100539 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_722
  · change initialPayment 723 ≤ initialValue ((point lo 4 1024 723+point lo 4 1024 724)/2)
    have hp : initialPayment 723 = (381455043807:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 723+point lo 4 1024 724)/2 = (161501731:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161501731:ℝ)/42188800) = (67942400:ℝ)/50478557 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_723
  · change initialPayment 724 ≤ initialValue ((point lo 4 1024 724+point lo 4 1024 725)/2)
    have hp : initialPayment 724 = (382164254609:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 724+point lo 4 1024 725)/2 = (161525869:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161525869:ℝ)/42188800) = (67942400:ℝ)/50454419 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_724
  · change initialPayment 725 ≤ initialValue ((point lo 4 1024 725+point lo 4 1024 726)/2)
    have hp : initialPayment 725 = (382874083857:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 725+point lo 4 1024 726)/2 = (161550007:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161550007:ℝ)/42188800) = (67942400:ℝ)/50430281 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_725
  · change initialPayment 726 ≤ initialValue ((point lo 4 1024 726+point lo 4 1024 727)/2)
    have hp : initialPayment 726 = (383584532167:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 726+point lo 4 1024 727)/2 = (32314829:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32314829:ℝ)/8437760) = (67942400:ℝ)/50406143 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_726
  · change initialPayment 727 ≤ initialValue ((point lo 4 1024 727+point lo 4 1024 728)/2)
    have hp : initialPayment 727 = (384295600159:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 727+point lo 4 1024 728)/2 = (161598283:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161598283:ℝ)/42188800) = (13588480:ℝ)/10076401 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_727
  · change initialPayment 728 ≤ initialValue ((point lo 4 1024 728+point lo 4 1024 729)/2)
    have hp : initialPayment 728 = (385007288452:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 728+point lo 4 1024 729)/2 = (161622421:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161622421:ℝ)/42188800) = (67942400:ℝ)/50357867 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_728
  · change initialPayment 729 ≤ initialValue ((point lo 4 1024 729+point lo 4 1024 730)/2)
    have hp : initialPayment 729 = (385719597665:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 729+point lo 4 1024 730)/2 = (161646559:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161646559:ℝ)/42188800) = (67942400:ℝ)/50333729 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_729
  · change initialPayment 730 ≤ initialValue ((point lo 4 1024 730+point lo 4 1024 731)/2)
    have hp : initialPayment 730 = (386432528421:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 730+point lo 4 1024 731)/2 = (161670697:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161670697:ℝ)/42188800) = (67942400:ℝ)/50309591 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_730
  · change initialPayment 731 ≤ initialValue ((point lo 4 1024 731+point lo 4 1024 732)/2)
    have hp : initialPayment 731 = (387146081342:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 731+point lo 4 1024 732)/2 = (32338967:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32338967:ℝ)/8437760) = (67942400:ℝ)/50285453 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_731
  · change initialPayment 732 ≤ initialValue ((point lo 4 1024 732+point lo 4 1024 733)/2)
    have hp : initialPayment 732 = (387860257051:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 732+point lo 4 1024 733)/2 = (161718973:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161718973:ℝ)/42188800) = (13588480:ℝ)/10052263 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_732
  · change initialPayment 733 ≤ initialValue ((point lo 4 1024 733+point lo 4 1024 734)/2)
    have hp : initialPayment 733 = (388575056171:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 733+point lo 4 1024 734)/2 = (161743111:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161743111:ℝ)/42188800) = (67942400:ℝ)/50237177 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_733
  · change initialPayment 734 ≤ initialValue ((point lo 4 1024 734+point lo 4 1024 735)/2)
    have hp : initialPayment 734 = (389290479329:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 734+point lo 4 1024 735)/2 = (161767249:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161767249:ℝ)/42188800) = (67942400:ℝ)/50213039 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_734
  · change initialPayment 735 ≤ initialValue ((point lo 4 1024 735+point lo 4 1024 736)/2)
    have hp : initialPayment 735 = (390006527151:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 735+point lo 4 1024 736)/2 = (161791387:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((161791387:ℝ)/42188800) = (67942400:ℝ)/50188901 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_735
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_045
